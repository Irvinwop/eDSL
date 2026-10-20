/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteScanBodies
import Lean

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ByteScanBodies
open X86 X86.Sequential Grading.ByteScan Corpus.V1

/-- An integration consequence for every admitted empty invocation, every
pointer and every AF stream. The raw policy must rule out ALL DATA reads,
including interior reads absent from the common result/frame contract. -/
theorem empty_no_data (compiler : ByteScanWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes compiler) input initial)
    (empty : input.value.values = []) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      result.state.registers .rax = 0 ∧ BufferCall.Post spec input initial result.state ∧
      ∀ read ∈ result.reads, PureCall.RawRead initial read := by
  obtain ⟨executions, policy⟩ := ByteScanBodies.raw compiler input initial pre
  obtain ⟨result, execution, post⟩ := executions choices
  have contract := post.result
  change BoundedNulLength input.value.values (result.state.registers .rax).toNat at contract
  rw [empty] at contract
  have zero : result.state.registers .rax = 0 :=
    BitVec.eq_of_toNat_eq ((BoundedNulLength.nil_iff _).mp contract)
  refine ⟨result, execution, zero, post, ?_⟩
  intro read member
  obtain ⟨_, _, _, _, _, _, _, _, _, allowed, _⟩ :=
    Grading.ReadOnlyPolicy.read_origin policy execution member
  rcases allowed with stack | ⟨_, buffer, member, span⟩
  · exact stack
  · have same : buffer = ⟨input.value.base, []⟩ := by simpa [spec, empty] using member
    subst buffer
    exact False.elim (BufferCall.Buffer.no_empty_span span)

/- These are small executions through the production byte decoder, operand
memory checks and executor, not premises of the universal theorem. Only exact
code, caller bytes and the listed data bytes are mapped. In particular the
first byte beyond a separate data fixture is inaccessible. No ELF/native or
resource-certificate claim is made by this synthetic memory fixture. -/
private def memory (compiler : ByteScanWindows.Compiler) (pointer : Word)
    (values : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + (ByteScanWindows.bytes compiler).length then
      (ByteScanWindows.bytes compiler)[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0, 0x30, 0, 0, 0, 0, 0, 0] : List Byte)[address.toNat - 0x2000]?
    else if pointer.toNat ≤ address.toNat then values[address.toNat - pointer.toNat]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧
    address.toNat < 0x1000 + (ByteScanWindows.bytes compiler).length)

private def initial (compiler : ByteScanWindows.Compiler) (pointer : Word)
    (values : List Byte) (count : Nat) : State where
  registers register := if register = .rsp then 0x2000
    else if register = .rdi then pointer
    else if register = .rsi then BitVec.ofNat 64 count
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0x246a
  memory := memory compiler pointer values

private def observed (compiler : ByteScanWindows.Compiler) (pointer : Word)
    (values : List Byte) (count : Nat) (af : Bool) : Option (Word × List Read × Word × Word) :=
  (Sequential.run (fun _ => af) 64 (initial compiler pointer values count)).toOption.map
    (fun result => (result.state.registers .rax, result.reads,
      result.state.registers .rsp, result.state.rip))

/-- Signed/high-byte mistakes and choosing a later duplicate NUL are visible
in both the return value and the exact operand footprint. -/
theorem high_bytes_earliest (compiler : ByteScanWindows.Compiler) (af : Bool) :
    observed compiler 0x4000 [0x80, 0xff, 0, 0] 4 af =
      some (2, [⟨.data, 0x4000, 1⟩, ⟨.data, 0x4001, 1⟩,
        ⟨.data, 0x4002, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- An inaccessible neighbor makes a speculative extra byte or widened load
fail; the correct bounded scan returns n after exactly n byte reads. -/
theorem all_nonzero_guard (compiler : ByteScanWindows.Compiler) (af : Bool) :
    observed compiler 0x4000 [0x80, 0xff] 2 af =
      some (2, [⟨.data, 0x4000, 1⟩, ⟨.data, 0x4001, 1⟩,
        ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- The final permitted byte must be examined; an early bound check that
skips it would return 3 instead of 2. -/
theorem final_nul (compiler : ByteScanWindows.Compiler) (af : Bool) :
    observed compiler 0x4000 [0x80, 0xff, 0] 3 af =
      some (2, [⟨.data, 0x4000, 1⟩, ⟨.data, 0x4001, 1⟩,
        ⟨.data, 0x4002, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Empty inputs return zero without even consulting an unmapped,
noncanonical data address. Only the original caller slot is read. -/
theorem empty_noncanonical (compiler : ByteScanWindows.Compiler) (af : Bool) :
    canonical 0x800000000000 = false ∧
    observed compiler 0x800000000000 [] 0 af =
      some (0, [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Readable executable bytes can also be data. Both first opcodes are
nonzero; scanning one byte must return 1 while instruction fetch succeeds. -/
theorem code_alias (compiler : ByteScanWindows.Compiler) (af : Bool) :
    observed compiler 0x1000 [] 1 af =
      some (1, [⟨.data, 0x1000, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- DATA1 and the actual original STACK8 may overlap compatibly. The NUL at
the first caller byte terminates the scan before RET reads the whole slot. -/
theorem caller_alias (compiler : ByteScanWindows.Compiler) (af : Bool) :
    observed compiler 0x2000 [] 2 af =
      some (0, [⟨.data, 0x2000, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

end EDSL.Tests.ByteScanBodies

elab "#audit_byte_scan_bodies" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``EDSL.X86.VCGen.ByteScan.CommonFrame.return_post,
    ``EDSL.X86.VCGen.ByteScan.read_byte, ``EDSL.X86.VCGen.ByteScan.next_nat,
    ``EDSL.X86.VCGen.ByteScan.next_rank, ``EDSL.X86.VCGen.ByteScan.advance,
    ``EDSL.Corpus.V1.ByteScanBodies.valid, ``EDSL.Corpus.V1.ByteScanBodies.gccAnnotations,
    ``EDSL.Corpus.V1.ByteScanBodies.clangAnnotations, ``EDSL.Corpus.V1.ByteScanBodies.generated,
    ``EDSL.Corpus.V1.ByteScanBodies.raw, ``EDSL.Corpus.V1.ByteScanBodies.semantics,
    ``EDSL.Corpus.V1.ByteScanBodies.dynamic_bound, ``EDSL.Tests.ByteScanBodies.empty_no_data,
    ``EDSL.Tests.ByteScanBodies.high_bytes_earliest, ``EDSL.Tests.ByteScanBodies.all_nonzero_guard,
    ``EDSL.Tests.ByteScanBodies.final_nul, ``EDSL.Tests.ByteScanBodies.empty_noncanonical,
    ``EDSL.Tests.ByteScanBodies.code_alias, ``EDSL.Tests.ByteScanBodies.caller_alias]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless allowed.contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"
    Lean.logInfo m!"Allowed named audit passed: {name}"

#print axioms EDSL.Corpus.V1.ByteScanBodies.semantics
#print axioms EDSL.Corpus.V1.ByteScanBodies.dynamic_bound
#print axioms EDSL.Tests.ByteScanBodies.empty_no_data
#audit_byte_scan_bodies
