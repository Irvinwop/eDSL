/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Domain
import EDSL.X86.Sequential.Execution
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingDomain
open X86 OS OS.AddressSpace OS.ArrayResources
open Grading.Domain

-- Exercise the public resource-to-machine adapters for every admitted byte
-- list. Neither constructor nor the resulting precondition requires a decoder,
-- a graph, or a successful execution. Permissions cover actual whole operands.
theorem every_candidate_pair (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    let witness := pair bytes positive bound
    Pair32.Pre bytes witness.initial witness.callA.values witness.callB.values witness.callA.target ∧
      witness.callA.values ≠ [] ∧ witness.callB.values ≠ [] ∧
      ∀ read ∈ Pair32.operandReads witness.initial witness.callA.values witness.callB.values,
        ReadPermission witness.shared witness.callA.worker read := by
  let witness := pair bytes positive bound
  have pre := Pair32.pre_of_admission witness.admitted witness.entry witness.stack
    witness.baseA witness.countA witness.baseB witness.countB
  rw [witness.code] at pre
  exact ⟨pre, witness.usefulA, witness.usefulB,
    fun _ member => Pair32.operandReads_permission witness.admitted
      witness.baseA witness.baseB witness.stack member⟩

theorem every_candidate_stride (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    let witness := stride bytes positive bound
    Stride32.Pre bytes witness.initial witness.call.values witness.count witness.call.target ∧
      0 < witness.count ∧
      ∀ read ∈ Stride32.operandReads witness.initial witness.count,
        ReadPermission witness.shared witness.call.worker read := by
  let witness := stride bytes positive bound
  have pre := Stride32.pre_of_admission witness.admitted witness.entry witness.stack
    witness.base witness.length witness.counter
  rw [witness.code] at pre
  exact ⟨pre, witness.useful, fun _ member => Stride32.operandReads_permission
    witness.admitted witness.length witness.base witness.stack member⟩

-- The generic theorem covers every current code cell, including trailing
-- bytes after an embedded RET and byte lists unsupported by any CFG importer.
theorem all_selected_cells (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (offset : Nat) (byte : Byte)
    (present : bytes[offset]? = some byte) :
    fetchByte (pair bytes positive bound).initial.memory
      ((pair bytes positive bound).initial.rip + BitVec.ofNat 64 offset) = .ok byte :=
  (every_candidate_pair bytes positive bound).1.code.2 offset byte present

theorem any_single_byte (byte : Byte) :
    fetchByte (pair [byte] (by simp) (by simp)).initial.memory 4096 = .ok byte := by
  exact all_selected_cells [byte] (by simp) (by simp) 0 byte rfl

theorem after_embedded_ret :
    fetchByte (pair [0xc3, 0xff] (by decide) (by decide)).initial.memory 4097 = .ok 0xff := by
  exact all_selected_cells [0xc3, 0xff] (by decide) (by decide) 1 0xff rfl

-- An arbitrary byte at the admitted upper bound must still be mapped and
-- executable at offset4095. This catches an accidental 64-byte semantic cap.
theorem maximum_span_last_byte (byte : Byte) :
    fetchByte (pair (List.replicate 4096 byte)
      (by rw [List.length_replicate]; decide)
      (by rw [List.length_replicate]; exact Nat.le_refl _)).initial.memory
      8191 = .ok byte := by
  exact all_selected_cells (List.replicate 4096 byte)
    (by rw [List.length_replicate]; decide)
    (by rw [List.length_replicate]; exact Nat.le_refl _)
    4095 byte (by rw [List.getElem?_replicate]; rfl)

theorem finite_executable_span (bytes : List Byte) (bound : bytes.length ≤ 4096)
    (address : Word) (far : 8192 ≤ address.toNat) :
    (toMemory (space bytes)).executable address = false := by
  have outside : ¬(codeRegion bytes).Contains address := by
    change ¬(4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    omega
  cases active : (toMemory (space bytes)).executable address with
  | false => rfl
  | true => exact False.elim (outside ((executable_iff bytes address).mp active))

-- Real borrowing reads compose allocation authority with the complete current
-- little-endian memory contents. In particular the logical odd trailing word
-- of the stride array is present and protected even though stride ignores it.
theorem full_inputs_readable (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.loadWord (pair bytes positive bound).shared 11 2 131084 = .ok 11 ∧
      Borrowing.loadWord (pair bytes positive bound).shared 11 3 196612 = .ok 5 := by
  constructor
  · exact element_loadWord (pair bytes positive bound).admitted.admittedA.resources
      (index := 3) rfl
  · exact element_loadWord (pair bytes positive bound).admitted.admittedB.resources
      (index := 1) rfl

theorem complete_return_slot (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    ReadPermission (pair bytes positive bound).shared 10 ⟨.stack, 65544, 8⟩ ∧
      readWord (pair bytes positive bound).initial.memory 65544 = .ok 8192 :=
  ⟨stackRead_permission (pair bytes positive bound).admitted.admittedA.resources,
    (every_candidate_pair bytes positive bound).1.stack⟩

-- Readable bytes of another live allocation do not extend this loan. A whole
-- operand crossing the end of the stack/input loan must also be rejected.
theorem authority_boundaries (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.loadWord (pair bytes positive bound).shared 11 3 131072 = .error .outsideLoan ∧
      Borrowing.loadWord (pair bytes positive bound).shared 11 2 131086 = .error .outsideLoan ∧
      Borrowing.loadWord (pair bytes positive bound).shared 11 1 65549 = .error .outsideLoan ∧
      Borrowing.loadWord (pair bytes positive bound).shared 12 2 131072 =
        .error (.authority .wrongBorrower) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem loans_block_mutation (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.mutate (pair bytes positive bound).shared (.store 7 ⟨2, 0⟩ 131072 0) =
      .error .borrowed ∧
      Borrowing.mutate (pair bytes positive bound).shared (.release 7 ⟨1, 0⟩) =
        .error .borrowed := by
  exact ⟨rfl, rfl⟩

-- A permission change outside every selected code/data/stack read still breaks
-- current admission. Comparing only successful read snapshots would miss it.
def extraExecute (bytes : List Byte) : X86.State :=
  { pairEntry bytes with memory :=
      { (pairEntry bytes).memory with executable := fun address =>
          if address = 8192 then true else (pairEntry bytes).memory.executable address } }

theorem coupling_rejects_added_permission (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    ¬ Admission (shared bytes) (callA bytes) (extraExecute bytes) := by
  intro admitted
  have equal := congrArg (fun memory : Memory => memory.executable 8192) admitted.coupled
  change true = (toMemory (space bytes)).executable 8192 at equal
  rw [finite_executable_span bytes bound 8192 (by decide)] at equal
  cases equal

-- Same-base, same-input-ID readonly aliasing remains admitted for arbitrary
-- candidate bytes; A/B separation is not a hidden restriction of the domain.
def aliasEntry (bytes : List Byte) : X86.State :=
  { pairEntry bytes with registers := fun register => match register with
      | .rdx => 131072
      | .rcx => 4
      | _ => (pairEntry bytes).registers register }

theorem compatible_alias (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Pair32.PairAdmission (shared bytes) (callA bytes) (callA bytes) (aliasEntry bytes) ∧
      Pair32.Pre bytes (aliasEntry bytes) valuesA valuesA 8192 := by
  have current : Admission (shared bytes) (callA bytes) (aliasEntry bytes) :=
    (pair bytes positive bound).admitted.admittedA.unchangedMemory rfl
  have admitted : Pair32.PairAdmission (shared bytes) (callA bytes) (callA bytes)
      (aliasEntry bytes) := ⟨current, current, .refl _⟩
  exact ⟨admitted, Pair32.pre_of_admission admitted rfl rfl rfl rfl rfl rfl⟩

-- Positivity belongs to OS code-loan admission, while the raw machine domain
-- independently includes an empty selected code span with useful inputs.
theorem raw_empty_inputs :
    Pair32.Pre [] (pairEntry []) valuesA valuesB 8192 ∧
      Stride32.Pre [] (strideEntry []) valuesA 2 8192 :=
  ⟨pair_raw_pre [] (by decide), stride_raw_pre [] (by decide)⟩

-- Truncated FF group bytes have useful current OS admissions for BOTH tasks.
-- Their actual one-step fault refutes even total execution with Post=True;
-- admission must never be mistaken for functional correctness.
theorem unsupported_current_inputs :
    Pair32.PairAdmission (shared [0xff]) (callA [0xff]) (callB [0xff])
        (pairEntry [0xff]) ∧
      Admission (shared [0xff]) (callA [0xff]) (strideEntry [0xff]) ∧
      Pair32.Pre [0xff] (pairEntry [0xff]) valuesA valuesB 8192 ∧
      Stride32.Pre [0xff] (strideEntry [0xff]) valuesA 2 8192 :=
  ⟨(pair [0xff] (by decide) (by decide)).admitted,
    (stride [0xff] (by decide) (by decide)).admitted,
    (every_candidate_pair [0xff] (by decide) (by decide)).1,
    (every_candidate_stride [0xff] (by decide) (by decide)).1⟩

theorem unsupported_steps (af : Bool) :
    Sequential.step af (pair [0xff] (by decide) (by decide)).initial =
        .error (.inaccessibleInstruction 4097) ∧
      Sequential.step af (stride [0xff] (by decide) (by decide)).initial =
        .error (.inaccessibleInstruction 4097) := by
  exact ⟨rfl, rfl⟩

theorem unsupported_pair_not_total :
    ¬ Sequential.AllExecutions (pair [0xff] (by decide) (by decide)).initial (fun _ => True) := by
  intro total
  have fault : Sequential.run (fun _ => false) 1 (pair [0xff] (by decide) (by decide)).initial =
      .error (.inaccessibleInstruction 4097) := by rfl
  have impossible := total.no_fault_prefix (fun _ => false) fault
  cases impossible

theorem unsupported_stride_not_total :
    ¬ Sequential.AllExecutions (stride [0xff] (by decide) (by decide)).initial (fun _ => True) := by
  intro total
  have fault : Sequential.run (fun _ => false) 1 (stride [0xff] (by decide) (by decide)).initial =
      .error (.inaccessibleInstruction 4097) := by rfl
  have impossible := total.no_fault_prefix (fun _ => false) fault
  cases impossible

#print axioms Grading.Domain.code_current
#print axioms Grading.Domain.world_valid
#print axioms Grading.Domain.shared_valid
#print axioms Grading.Domain.pair
#print axioms Grading.Domain.stride
#print axioms every_candidate_pair
#print axioms every_candidate_stride
#print axioms maximum_span_last_byte
#print axioms unsupported_pair_not_total
#print axioms unsupported_stride_not_total

end EDSL.Tests.GradingDomain

#audit_edsl
