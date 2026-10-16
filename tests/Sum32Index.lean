/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Index
import EDSL.Audit

namespace EDSL.Tests.Sum32Index
open X86 Sum32

/-- Complete final linked Clang 18 scalar -Oz window from the project's
owned sum32 fixture, as recorded in artifacts/sum32-fixtures/clang. -/
def clangBytes : List Byte :=
  [0x31, 0xc0, 0x31, 0xc9, 0x48, 0x39, 0xce, 0x74, 0x08,
   0x03, 0x04, 0x8f, 0x48, 0xff, 0xc1, 0xeb, 0xf3, 0xc3]

def clangPlan : Plan where
  mode := .index
  prologue := [⟨0, .xorSelf32 .rax⟩, ⟨2, .xorSelf32 .rcx⟩]
  header := 4
  branch := ⟨7, 8⟩
  load := 9
  updates := [⟨12, .inc64 .rcx⟩]
  back := ⟨15, 0xf3⟩
  exit := 17

theorem clangValid : Valid clangBytes clangPlan := checkPlan_sound (by decide)

/-- The real compiler window instantiates the generic theorem for arbitrary
current arrays, accumulated values, memory, count bounds and AF streams. -/
example {base : Word} {state : State} {values : List (BitVec 32)}
    {accumulator : BitVec 32} {target : Word} {consumed total : Nat}
    (header : IndexHeader clangBytes clangPlan base state values accumulator target consumed total)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices state result ∧
      LoopPost state accumulator values target result.state ∧
      result.instructions = 5 * values.length + 3 ∧
      result.reads = indexReads state consumed values :=
  index_loop clangValid rfl header choices

/-- A different, longer prologue changes every loop PC. This catches a
checker accidentally tied to the Clang bytes or its absolute node offsets. -/
def mixedBytes : List Byte :=
  [0x31, 0xc9, 0xb8, 0, 0, 0, 0, 0x48, 0x39, 0xce, 0x74, 0x08,
   0x03, 0x04, 0x8f, 0x48, 0xff, 0xc1, 0xeb, 0xf3, 0xc3]

def mixedPlan : Plan where
  mode := .index
  prologue := [⟨0, .xorSelf32 .rcx⟩, ⟨2, .legacy (.mov32 .rax 0)⟩]
  header := 7
  branch := ⟨10, 8⟩
  load := 12
  updates := [⟨15, .inc64 .rcx⟩]
  back := ⟨18, 0xf3⟩
  exit := 20

theorem mixedValid : Valid mixedBytes mixedPlan := checkPlan_sound (by decide)

example {base : Word} {state : State} {values : List (BitVec 32)}
    {accumulator : BitVec 32} {target : Word} {consumed total : Nat}
    (header : IndexHeader mixedBytes mixedPlan base state values accumulator target consumed total) :
    Sequential.AllExecutions state (fun result =>
      LoopPost state accumulator values target result.state ∧
      result.instructions = 5 * values.length + 3 ∧
      result.reads = indexReads state consumed values) :=
  index_all_executions mixedValid rfl header

/-- Only the current suffix is mapped. In particular no low-32-bit alias
of its high-index input address is readable. Code ends at the actual RET. -/
def memory : Memory where
  read address :=
    if address.toNat < clangBytes.length then clangBytes[address.toNat]?
    else if 4096 ≤ address.toNat ∧ address.toNat < 4104 then
      [0, 4, 0, 0, 0, 0, 0, 0][address.toNat - 4096]?
    else if 0x400002000 ≤ address.toNat ∧ address.toNat < 0x400002010 then
      [0xff, 0xff, 0xff, 0xff, 1, 0, 0, 0,
       0, 0, 0, 0x80, 0, 0, 0, 0x80][address.toNat - 0x400002000]?
    else none
  executable address := decide (address.toNat < clangBytes.length)
  writable _ := false

theorem currentCode : CodeAt memory 0 clangBytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  have small : offset < 18 := by
    have := List.getElem?_eq_some_iff.mp present
    obtain ⟨inside, _⟩ := this
    exact inside
  have fits : offset < 2^64 := by omega
  have inside : offset < clangBytes.length := small
  have canonicalOffset : canonical (BitVec.ofNat 64 offset) = true := by
    simp only [canonical, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    exact decide_eq_true (Or.inl (by omega))
  simpa [fetchByte, memory, Nat.mod_eq_of_lt fits, canonicalOffset, inside] using
    (List.getElem?_eq_some_iff.mp present).2

def entry (empty : Bool) : State where
  registers register :=
    if register = .rax then 7
    else if register = .rcx then 0x100000000
    else if register = .rsi then if empty then 0x100000000 else 0x100000004
    else if register = .rdi then if empty then 0x800000000000 else 8192
    else if register = .rsp then 4096
    else 0xfedcba9876543210
  rip := 4
  flags := 0xa00000000602
  memory := memory

def values : List (BitVec 32) := [0xffffffff, 1, 0x80000000, 0x80000000]

theorem emptyHeader : IndexHeader clangBytes clangPlan 0 (entry true) [] 7 1024
    0x100000000 0x100000000 := by
  refine {
    code := currentCode
    pc := rfl
    accumulator := rfl
    stack := rfl
    canonicalTarget := by decide
    canonicalStackAfter := by decide
    array := ArrayAt.nil _ _
    count := rfl
    index := rfl
    remaining := rfl
    countBound := by decide }

theorem wrapHeader : IndexHeader clangBytes clangPlan 0 (entry false) values 7 1024
    0x100000000 0x100000004 := by
  refine {
    code := currentCode
    pc := rfl
    accumulator := rfl
    stack := rfl
    canonicalTarget := by decide
    canonicalStackAfter := by decide
    array := ?_
    count := rfl
    index := rfl
    remaining := rfl
    countBound := by decide }
  intro index value present
  have small : index < 4 := by
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp present
    exact inside
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [values] at present <;>
    subst value <;> rfl

/-- Empty input needs no readable or canonical input pointer and reads only
the actual eight-byte return address, independently of the AF stream. -/
example (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices (entry true) result ∧
      result.state.registers .rax = 7 ∧ result.instructions = 3 ∧
      result.reads = [⟨.stack, 4096, 8⟩] := by
  obtain ⟨result, execution, post, cost, reads⟩ := index_loop clangValid rfl emptyHeader choices
  exact ⟨result, execution, by simpa using post.value, cost, reads⟩

/-- The mathematical suffix sums to 2^33 and hence contributes zero modulo
2^32. The nonzero accumulator survives, with the full RAX zero extension. -/
example (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices (entry false) result ∧
      result.state.registers .rax = 7 ∧ result.instructions = 23 ∧
      result.reads = [⟨.data, 0x400002000, 4⟩, ⟨.data, 0x400002004, 4⟩,
        ⟨.data, 0x400002008, 4⟩, ⟨.data, 0x40000200c, 4⟩, ⟨.stack, 4096, 8⟩] := by
  obtain ⟨result, execution, post, cost, reads⟩ := index_loop clangValid rfl wrapHeader choices
  exact ⟨result, execution, post.value, cost, reads⟩

/-- Also run the actual evaluator on the real bytes with a nonconstant
choice stream. This checks real termination, full-width addressing, current
stack return and the independent wraparound result together. -/
example : (Sequential.run (fun n => decide (n % 3 = 1)) 23 (entry false)).map
    (fun result => (result.state.registers .rax, result.state.rip,
      result.state.registers .rsp, result.instructions, result.reads)) =
    .ok (7, 1024, 4104, 23,
      [⟨.data, 0x400002000, 4⟩, ⟨.data, 0x400002004, 4⟩,
       ⟨.data, 0x400002008, 4⟩, ⟨.data, 0x40000200c, 4⟩, ⟨.stack, 4096, 8⟩]) := by rfl

#audit_edsl

end EDSL.Tests.Sum32Index
