/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.BufferCall
import EDSL.X86.Sequential.ByteOrder
import EDSL.Grading.BufferTask

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.ByteComparison
open Sequential Grading.ByteComparison

/-- A typed view of the fixed registered input, so generated expressions do
not rely on unfolding a spec record while matching dependent projections. -/
def view (value : spec.Input) : Input := value

/-- Shared paired-buffer frame. All RAM and permission maps, full-width
arguments, caller slot, callee saves and nonarithmetic flags are retained. -/
structure CommonFrame (initial state : State) : Prop where
  memory : state.memory = initial.memory
  registers : ∀ register, register ≠ .rax → register ≠ .rcx → register ≠ .r8 →
    state.registers register = initial.registers register
  flags : state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem commonFrame_iff (initial state : State) : CommonFrame initial state ↔
    state.memory = initial.memory ∧
    (∀ register, register ≠ .rax → register ≠ .rcx → register ≠ .r8 →
      state.registers register = initial.registers register) ∧
    state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask :=
  ⟨fun f => ⟨f.memory, f.registers, f.flags⟩, fun ⟨m, r, f⟩ => ⟨m, r, f⟩⟩

theorem CommonFrame.refl (initial : State) : CommonFrame initial initial :=
  ⟨rfl, fun _ _ _ _ => rfl, rfl⟩

theorem CommonFrame.rsp {initial state : State} (f : CommonFrame initial state) :
    state.registers .rsp = initial.registers .rsp :=
  f.registers .rsp (by decide) (by decide) (by decide)
theorem CommonFrame.rdi {initial state : State} (f : CommonFrame initial state) :
    state.registers .rdi = initial.registers .rdi :=
  f.registers .rdi (by decide) (by decide) (by decide)
theorem CommonFrame.rsi {initial state : State} (f : CommonFrame initial state) :
    state.registers .rsi = initial.registers .rsi :=
  f.registers .rsi (by decide) (by decide) (by decide)
theorem CommonFrame.rdx {initial state : State} (f : CommonFrame initial state) :
    state.registers .rdx = initial.registers .rdx :=
  f.registers .rdx (by decide) (by decide) (by decide)

theorem saved_different (register : Register) (saved : register ∈ PureCall.calleeSaved) :
    register ≠ .rsp ∧ register ≠ .rax ∧ register ≠ .rcx ∧ register ≠ .r8 := by
  simp only [PureCall.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

variable {bytes : List Byte} {input : BufferCall.Invocation spec} {initial state : State}

theorem same_length (pre : BufferCall.Pre spec bytes input initial) :
    (view input.value).left.length = (view input.value).right.length := pre.domain.1

theorem count_small (pre : BufferCall.Pre spec bytes input initial) :
    (view input.value).left.length < 2^64 := pre.domain.2

theorem count_nat (pre : BufferCall.Pre spec bytes input initial) :
    (BitVec.ofNat 64 (view input.value).left.length).toNat = (view input.value).left.length := by
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (count_small pre)]

theorem left_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rdi = (view input.value).leftBase :=
  (Grading.ByteComparison.bound_iff _ _).mp pre.arguments |>.1
theorem right_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rsi = (view input.value).rightBase :=
  (Grading.ByteComparison.bound_iff _ _).mp pre.arguments |>.2.1
theorem count_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rdx = BitVec.ofNat 64 (view input.value).left.length :=
  (Grading.ByteComparison.bound_iff _ _).mp pre.arguments |>.2.2

/-- One real DATA1 read fits its exact initial snapshot. The current frame
transports complete memory; readable neighbors cannot enlarge this authority. -/
theorem read_byte (pre : BufferCall.Pre spec bytes input initial)
    (frame : CommonFrame initial state) (buffer : BufferCall.Buffer)
    (member : buffer ∈ spec.buffers input.value) {index : Nat}
    (inside : index < buffer.bytes.length) :
    ∃ byte, buffer.bytes[index]? = some byte ∧
      readDataByte state.memory (buffer.base + BitVec.ofNat 64 index) = .ok byte ∧
      BufferCall.RawRead spec input initial ⟨.data, buffer.base + BitVec.ofNat 64 index, 1⟩ := by
  have snapshot := pre.buffers buffer member
  have present := List.getElem?_eq_getElem inside
  refine ⟨_, present, ?_, Or.inr ⟨rfl, buffer, member, ?_⟩⟩
  · rw [frame.memory]
    exact snapshot.2 index _ present
  · change 0 < 1 ∧ _ ≤ _ ∧ _ + 1 ≤ _
    rw [BufferCall.Buffer.offset_address snapshot inside]
    exact ⟨by decide, by omega, by omega⟩

/-- Both loads have positive width one, with no alignment or disjointness
premise. At zero length this helper is never required. -/
theorem read_pair (pre : BufferCall.Pre spec bytes input initial)
    (frame : CommonFrame initial state) {index : Nat}
    (inside : index < (view input.value).left.length) :
    ∃ a b, (view input.value).left[index]? = some a ∧ (view input.value).right[index]? = some b ∧
      readDataByte state.memory ((view input.value).leftBase + BitVec.ofNat 64 index) = .ok a ∧
      readDataByte state.memory ((view input.value).rightBase + BitVec.ofNat 64 index) = .ok b ∧
      BufferCall.RawRead spec input initial
        ⟨.data, (view input.value).leftBase + BitVec.ofNat 64 index, 1⟩ ∧
      BufferCall.RawRead spec input initial
        ⟨.data, (view input.value).rightBase + BitVec.ofNat 64 index, 1⟩ := by
  obtain ⟨a, atA, readA, allowedA⟩ := read_byte pre frame (leftBuffer (view input.value))
    (by
      change leftBuffer (view input.value) ∈ [leftBuffer (view input.value), rightBuffer (view input.value)]
      simp) inside
  obtain ⟨b, atB, readB, allowedB⟩ := read_byte pre frame (rightBuffer (view input.value))
    (by
      change rightBuffer (view input.value) ∈ [leftBuffer (view input.value), rightBuffer (view input.value)]
      simp) (by simpa only [rightBuffer, ← same_length pre] using inside)
  exact ⟨a, b, atA, atB, readA, readB, allowedA, allowedB⟩

abbrev EqualPrefix (input : Input) (index : Nat) : Prop :=
  Grading.FirstMatch.Prefix (input.left.zip input.right) (fun pair => pair.1 != pair.2) index

theorem next_nat {count : Nat} {index : Word} (small : count < 2^64)
    (inside : index.toNat < count) : (index + 1).toNat = index.toNat + 1 := by
  have sum : index.toNat + 1 < 2^64 := by omega
  rw [BitVec.toNat_add]
  change (index.toNat + 1) % 2^64 = index.toNat + 1
  exact Nat.mod_eq_of_lt sum

theorem next_rank {count : Nat} {index : Word} (small : count < 2^64)
    (inside : index.toNat < count) : count - (index + 1).toNat < count - index.toNat := by
  rw [next_nat small inside]
  omega

theorem advance {index : Word} {a b : Byte}
    (pre : BufferCall.Pre spec bytes input initial)
    (inside : index.toNat < (view input.value).left.length)
    (scanned : EqualPrefix (view input.value) index.toNat)
    (leftAt : (view input.value).left[index.toNat]? = some a)
    (rightAt : (view input.value).right[index.toNat]? = some b) (equal : a = b) :
    EqualPrefix (view input.value) (index + 1).toNat := by
  rw [next_nat (count_small pre) inside]
  exact scanned.advance (List.getElem?_zip_eq_some (z := (a, b)) |>.mpr ⟨leftAt, rightAt⟩)
    (by simp [equal])

/-- Exhaustion and the first unequal pair are discharged against the
independent unsigned List.Lex sign contract, observing only signed low32. -/
theorem finish_bound {index : Nat} {actual : Word}
    (pre : BufferCall.Pre spec bytes input initial)
    (scanned : EqualPrefix (view input.value) index) (done : index = (view input.value).left.length)
    (returned : returnValue actual = 0) : spec.result input.value actual := by
  subst index
  apply result_of_exhaustion (same_length pre) _ returned
  apply scanned.finish_bound
  simp only [List.length_zip, ← same_length pre, Nat.min_self]

theorem finish_hit {index : Nat} {a b : Byte} {actual : Word}
    (pre : BufferCall.Pre spec bytes input initial)
    (scanned : EqualPrefix (view input.value) index)
    (leftAt : (view input.value).left[index]? = some a) (rightAt : (view input.value).right[index]? = some b)
    (different : a ≠ b) (returned : returnValue actual = Grading.ByteOrder.signedDifference a b) :
    spec.result input.value actual :=
  result_at_first_unequal (same_length pre) (Grading.ByteOrder.paired_prefix_equal scanned)
    leftAt rightAt different returned

theorem sub_return (a b : Byte) :
    returnValue ((a.setWidth 32 - b.setWidth 32).setWidth 64) =
      Grading.ByteOrder.signedDifference a b := by
  simp [returnValue, Grading.ByteOrder.signedDifference]

end EDSL.X86.VCGen.ByteComparison
