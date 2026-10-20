/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.IndexSearchBodies
import Lean

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.IndexSearchBodies
open X86 X86.Sequential Corpus.V1
open X86.VCGen.IndexSearch
open Grading.IndexSearch

/-- The universal policy, specialized to empty inputs, allows only the
original STACK8 at every reachable prefix, for BOTH operations/layouts. -/
theorem empty_policy (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (IndexSearchBodies.width op))) (initial : State)
    (pre : BufferCall.Pre (spec (IndexSearchBodies.width op)) (IndexSearchWindows.bytes compiler op) input initial)
    (empty : values (IndexSearchBodies.width op) input.value = []) :
    Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
      (fun _ read => PureCall.RawRead initial read) := by
  have emptyBuffers : ∀ buffer ∈ (spec (IndexSearchBodies.width op)).buffers input.value,
      buffer.bytes = [] := by
    cases op with
    | byte =>
      intro buffer member
      have same : buffer = byteBuffer input.value := by simpa [IndexSearchBodies.width, spec, byteSpec] using member
      subst buffer
      exact empty
    | u32 =>
      intro buffer member
      have same : buffer = u32Buffer input.value := by simpa [IndexSearchBodies.width, spec, u32Spec] using member
      subst buffer
      change input.value.values = [] at empty
      simp [u32Buffer, empty]
  obtain ⟨_, policy⟩ := IndexSearchBodies.raw compiler op input initial pre
  apply policy.mono (fun _ same => same)
  intro before read allowed
  rcases allowed with stack | data
  · exact stack
  · exact False.elim (BufferCall.DataRead.no_empty emptyBuffers read data)

/-- Every admitted empty call returns full64 SIZE_MAX, with no DATA reads,
regardless of data pointer, relocation, initial flags or AF stream. -/
theorem empty_no_data (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (IndexSearchBodies.width op))) (initial : State)
    (pre : BufferCall.Pre (spec (IndexSearchBodies.width op)) (IndexSearchWindows.bytes compiler op) input initial)
    (empty : values (IndexSearchBodies.width op) input.value = []) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      result.state.registers .rax = sizeMax ∧
      BufferCall.Post (spec (IndexSearchBodies.width op)) input initial result.state ∧
      ∀ read ∈ result.reads, PureCall.RawRead initial read := by
  obtain ⟨executions, _⟩ := IndexSearchBodies.raw compiler op input initial pre
  obtain ⟨result, execution, post⟩ := executions choices
  have mathematical := (result_iff _ _ _).mp post.result
  rw [empty] at mathematical
  have maximum := (Result.nil_iff _ _).mp mathematical
  refine ⟨result, execution, maximum, post, ?_⟩
  intro read member
  obtain ⟨_, _, _, _, _, _, _, _, _, allowed, _⟩ :=
    Grading.ReadOnlyPolicy.read_origin (empty_policy compiler op input initial pre empty) execution member
  exact allowed

/- Small integration executions use only production decodeAt/run, exact frozen
window bytes, an original caller slot and explicit independent wire bytes. The
first byte after each wire list is inaccessible. These fixed test budgets are
not universal preconditions, and establish no ELF/resource/native certificate. -/
private def memory (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (pointer : Word) (wire : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + (IndexSearchWindows.bytes compiler op).length then
      (IndexSearchWindows.bytes compiler op)[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0, 0x30, 0, 0, 0, 0, 0, 0] : List Byte)[address.toNat - 0x2000]?
    else if pointer.toNat ≤ address.toNat then wire[address.toNat - pointer.toNat]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧
    address.toNat < 0x1000 + (IndexSearchWindows.bytes compiler op).length)

private def initial (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (pointer : Word) (wire : List Byte) (count : Nat) (needle : Word) : State where
  registers register := if register = .rsp then 0x2000
    else if register = .rdi then pointer
    else if register = .rsi then BitVec.ofNat 64 count
    else if register = .rdx then needle
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0x246a
  memory := memory compiler op pointer wire

private def observed (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (pointer : Word) (wire : List Byte) (count : Nat) (needle : Word) (af : Bool) :
    Option (Word × List Read × Word × Word × Word) :=
  (Sequential.run (fun _ => af) 64 (initial compiler op pointer wire count needle)).toOption.map
    (fun result => (result.state.registers .rax, result.reads,
      result.state.registers .rsp, result.state.rip, result.state.registers .rdx))

/-- Low8 key binding ignores dirty high RDX bits, retains RDX, and stops at
the FIRST duplicate, rather than the later matching byte. -/
theorem byte_first_duplicate (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .byte 0x100000001 [0x80, 0xff, 0xef, 0xef] 4 0x123456789abcdeef af =
      some (2, [⟨.data, 0x100000001, 1⟩, ⟨.data, 0x100000002, 1⟩,
        ⟨.data, 0x100000003, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0x123456789abcdeef) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Independent little-endian wire words are 0xef, 0x100ef, 0x800000ef,
0x800000ef. The first two have the same low16/low8 as the key, so narrowed
comparison returns the wrong index. Upper RDX bits must be ignored/retained. -/
theorem u32_first_duplicate (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .u32 0x100000001
      [0xef, 0, 0, 0, 0xef, 0, 1, 0, 0xef, 0, 0, 0x80, 0xef, 0, 0, 0x80]
      4 0xfeedface800000ef af =
      some (2, [⟨.data, 0x100000001, 4⟩, ⟨.data, 0x100000005, 4⟩,
        ⟨.data, 0x100000009, 4⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xfeedface800000ef) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Exhaustion returns SIZE_MAX in all 64 bits, reads exactly the admitted
bytes and never consults the inaccessible neighbor. -/
theorem byte_absent_guard (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .byte 0x4000 [0x80, 0xff] 2 0xfeed0000000000ef af =
      some (0xffffffffffffffff, [⟨.data, 0x4000, 1⟩, ⟨.data, 0x4001, 1⟩,
        ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xfeed0000000000ef) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Unaligned, above-32-bit DATA4 exhaustion cannot read a third element or
widen the final load into the inaccessible byte following the wire list. -/
theorem u32_absent_guard (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .u32 0x100000001 [0xef, 0, 0, 0, 0xef, 0, 1, 0] 2 0xfeedface800000ef af =
      some (0xffffffffffffffff, [⟨.data, 0x100000001, 4⟩, ⟨.data, 0x100000005, 4⟩,
        ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xfeedface800000ef) := by
  cases compiler <;> cases af <;> decide +kernel

/-- The final permitted byte must be tested, without a widened operand. -/
theorem byte_final (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .byte 0x4000 [0x80, 0xff, 0xef] 3 0x123456789abcdeef af =
      some (2, [⟨.data, 0x4000, 1⟩, ⟨.data, 0x4001, 1⟩, ⟨.data, 0x4002, 1⟩,
        ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0x123456789abcdeef) := by
  cases compiler <;> cases af <;> decide +kernel

/-- The final word's fourth byte distinguishes the match, and the fifth byte
is inaccessible. Neither a low16 comparison nor a widened read can pass. -/
theorem u32_final (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .u32 0x100000001 [0xef, 0, 0, 0, 0xef, 0, 0, 0x80] 2 0xfeedface800000ef af =
      some (1, [⟨.data, 0x100000001, 4⟩, ⟨.data, 0x100000005, 4⟩,
        ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xfeedface800000ef) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Neither zero-length operation validates or reads the unmapped,
noncanonical pointer. Only the original caller slot is an operand read. -/
theorem empty_noncanonical (compiler : IndexSearchWindows.Compiler)
    (op : IndexSearchWindows.Operation) (af : Bool) :
    canonical 0x800000000000 = false ∧
    observed compiler op 0x800000000000 [] 0 0xfedcba9876543210 af =
      some (0xffffffffffffffff, [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xfedcba9876543210) := by
  cases compiler <;> cases op <;> cases af <;> decide +kernel

/-- Data and original caller bytes can alias compatibly for both widths. -/
theorem caller_alias (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .byte 0x2000 [] 2 0xabcdef0000000000 af =
      some (0, [⟨.data, 0x2000, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xabcdef0000000000) ∧
    observed compiler .u32 0x2000 [] 2 0xabcdef0000003000 af =
      some (0, [⟨.data, 0x2000, 4⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xabcdef0000003000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Executable bytes may also supply ordinary read-only data. -/
theorem code_alias (compiler : IndexSearchWindows.Compiler) (af : Bool) :
    observed compiler .byte 0x1000 [] 1 0xabcdef0000000000 af =
      some (0xffffffffffffffff, [⟨.data, 0x1000, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xabcdef0000000000) ∧
    observed compiler .u32 0x1000 [] 1 0xabcdef00feedface af =
      some (0xffffffffffffffff, [⟨.data, 0x1000, 4⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000, 0xabcdef00feedface) := by
  cases compiler <;> cases af <;> decide +kernel

end EDSL.Tests.IndexSearchBodies

elab "#audit_index_search_bodies" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``EDSL.X86.VCGen.IndexSearch.registered_spec,
    ``EDSL.X86.VCGen.IndexSearch.result_iff,
    ``EDSL.X86.VCGen.IndexSearch.commonFrame_iff,
    ``EDSL.X86.VCGen.IndexSearch.CommonFrame.refl,
    ``EDSL.X86.VCGen.IndexSearch.CommonFrame.rsp,
    ``EDSL.X86.VCGen.IndexSearch.CommonFrame.rdi,
    ``EDSL.X86.VCGen.IndexSearch.CommonFrame.rsi,
    ``EDSL.X86.VCGen.IndexSearch.CommonFrame.rdx,
    ``EDSL.X86.VCGen.IndexSearch.saved_different,
    ``EDSL.X86.VCGen.IndexSearch.count_small,
    ``EDSL.X86.VCGen.IndexSearch.count_nat,
    ``EDSL.X86.VCGen.IndexSearch.base_argument,
    ``EDSL.X86.VCGen.IndexSearch.count_argument,
    ``EDSL.X86.VCGen.IndexSearch.key_argument,
    ``EDSL.X86.VCGen.IndexSearch.comparisonFlags_zero,
    ``EDSL.X86.VCGen.IndexSearch.comparisonFlags_preserves,
    ``EDSL.X86.VCGen.IndexSearch.scaled_index,
    ``EDSL.X86.VCGen.IndexSearch.read_comparison,
    ``EDSL.X86.VCGen.IndexSearch.next_nat,
    ``EDSL.X86.VCGen.IndexSearch.next_rank,
    ``EDSL.X86.VCGen.IndexSearch.advance,
    ``EDSL.X86.VCGen.IndexSearch.finish_hit,
    ``EDSL.X86.VCGen.IndexSearch.finish_bound,
    ``EDSL.X86.VCGen.IndexSearch.wp_next,
    ``EDSL.Corpus.V1.IndexSearchBodies.gcc_checked,
    ``EDSL.Corpus.V1.IndexSearchBodies.clang_checked,
    ``EDSL.Corpus.V1.IndexSearchBodies.gcc_valid,
    ``EDSL.Corpus.V1.IndexSearchBodies.clang_valid,
    ``EDSL.Corpus.V1.IndexSearchBodies.gccAnnotations,
    ``EDSL.Corpus.V1.IndexSearchBodies.clangAnnotations,
    ``EDSL.Corpus.V1.IndexSearchBodies.valid,
    ``EDSL.Corpus.V1.IndexSearchBodies.annotations,
    ``EDSL.Corpus.V1.IndexSearchBodies.entry_invariant,
    ``EDSL.Corpus.V1.IndexSearchBodies.generated,
    ``EDSL.Corpus.V1.IndexSearchBodies.raw,
    ``EDSL.Corpus.V1.IndexSearchBodies.semantics,
    ``EDSL.Corpus.V1.IndexSearchBodies.dynamic_bound,
    ``EDSL.Corpus.V1.IndexSearchBodies.gcc_byte_semantics,
    ``EDSL.Corpus.V1.IndexSearchBodies.gcc_u32_semantics,
    ``EDSL.Corpus.V1.IndexSearchBodies.clang_byte_semantics,
    ``EDSL.Corpus.V1.IndexSearchBodies.clang_u32_semantics,
    ``EDSL.Tests.IndexSearchBodies.empty_policy,
    ``EDSL.Tests.IndexSearchBodies.empty_no_data,
    ``EDSL.Tests.IndexSearchBodies.byte_first_duplicate,
    ``EDSL.Tests.IndexSearchBodies.u32_first_duplicate,
    ``EDSL.Tests.IndexSearchBodies.byte_absent_guard,
    ``EDSL.Tests.IndexSearchBodies.u32_absent_guard,
    ``EDSL.Tests.IndexSearchBodies.byte_final,
    ``EDSL.Tests.IndexSearchBodies.u32_final,
    ``EDSL.Tests.IndexSearchBodies.empty_noncanonical,
    ``EDSL.Tests.IndexSearchBodies.caller_alias,
    ``EDSL.Tests.IndexSearchBodies.code_alias]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless allowed.contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"
    Lean.logInfo m!"Allowed named audit passed: {name}"

#print axioms EDSL.Corpus.V1.IndexSearchBodies.gcc_byte_semantics
#print axioms EDSL.Corpus.V1.IndexSearchBodies.gcc_u32_semantics
#print axioms EDSL.Corpus.V1.IndexSearchBodies.clang_byte_semantics
#print axioms EDSL.Corpus.V1.IndexSearchBodies.clang_u32_semantics
#print axioms EDSL.Corpus.V1.IndexSearchBodies.dynamic_bound
#print axioms EDSL.Tests.IndexSearchBodies.empty_policy
#audit_index_search_bodies
