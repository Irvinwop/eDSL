/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ByteComparison
import EDSL.X86.Sequential.ByteComparePadding
import EDSL.X86.Sequential.Low8
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Grading.ByteEquality

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.ByteEquality
open Sequential Grading.ByteEquality

abbrev CommonFrame := ByteComparison.CommonFrame
abbrev commonFrame_iff := ByteComparison.commonFrame_iff
abbrev EqualPrefix := ByteComparison.EqualPrefix
abbrev next_nat := @ByteComparison.next_nat
abbrev next_rank := @ByteComparison.next_rank
abbrev saved_different := ByteComparison.saved_different

def view (value : spec.Input) : Input := value

/-- Result-only view: snapshots, bindings, original return and all preconditions
are identical; neither task's successful result is assumed. -/
def comparisonInvocation (input : BufferCall.Invocation spec) :
    BufferCall.Invocation Grading.ByteComparison.spec := ⟨input.value,input.returnAddress⟩

theorem comparisonPre {bytes : List Byte} {input : BufferCall.Invocation spec} {initial : State}
    (pre : BufferCall.Pre spec bytes input initial) :
    BufferCall.Pre Grading.ByteComparison.spec bytes (comparisonInvocation input) initial :=
  ⟨pre.domain,pre.arguments,pre.buffers,pre.code,pre.stack,pre.returnCanonical,
    pre.stackBound,pre.postStackCanonical⟩

variable {bytes : List Byte} {input : BufferCall.Invocation spec} {initial state : State}

theorem same_length (pre : BufferCall.Pre spec bytes input initial) :
    (view input.value).left.length = (view input.value).right.length :=
  ByteComparison.same_length (comparisonPre pre)
theorem count_small (pre : BufferCall.Pre spec bytes input initial) :
    (view input.value).left.length < 2^64 :=
  ByteComparison.count_small (comparisonPre pre)
theorem count_nat (pre : BufferCall.Pre spec bytes input initial) :
    (BitVec.ofNat 64 (view input.value).left.length).toNat = (view input.value).left.length :=
  ByteComparison.count_nat (comparisonPre pre)
theorem left_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rdi = (view input.value).leftBase :=
  ByteComparison.left_argument (comparisonPre pre)
theorem right_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rsi = (view input.value).rightBase :=
  ByteComparison.right_argument (comparisonPre pre)
theorem count_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rdx = BitVec.ofNat 64 (view input.value).left.length :=
  ByteComparison.count_argument (comparisonPre pre)

/-- Reuse the actual paired DATA1 observations and original read authority.
The result-only adapter creates no new read or ownership rule. -/
theorem read_pair (pre : BufferCall.Pre spec bytes input initial)
    (frame : CommonFrame initial state) {index : Nat}
    (inside : index < (view input.value).left.length) :
    ∃ a b, (view input.value).left[index]? = some a ∧ (view input.value).right[index]? = some b ∧
      readDataByte state.memory ((view input.value).leftBase + BitVec.ofNat 64 index) = .ok a ∧
      readDataByte state.memory ((view input.value).rightBase + BitVec.ofNat 64 index) = .ok b ∧
      BufferCall.RawRead spec input initial ⟨.data,(view input.value).leftBase + BitVec.ofNat 64 index,1⟩ ∧
      BufferCall.RawRead spec input initial ⟨.data,(view input.value).rightBase + BitVec.ofNat 64 index,1⟩ :=
  ByteComparison.read_pair (comparisonPre pre) frame inside

theorem advance {index : Word} {a b : Byte}
    (pre : BufferCall.Pre spec bytes input initial)
    (inside : index.toNat < (view input.value).left.length)
    (scanned : EqualPrefix (view input.value) index.toNat)
    (leftAt : (view input.value).left[index.toNat]? = some a)
    (rightAt : (view input.value).right[index.toNat]? = some b) (equal : a = b) :
    EqualPrefix (view input.value) (index + 1).toNat :=
  ByteComparison.advance (comparisonPre pre) inside scanned leftAt rightAt equal

theorem finish_bound {index : Nat} {actual : Word}
    (pre : BufferCall.Pre spec bytes input initial)
    (scanned : EqualPrefix (view input.value) index)
    (done : index = (view input.value).left.length) (returned : returnValue actual = 1) :
    spec.result input.value actual :=
  result_of_prefix_exhaustion (same_length pre) scanned done returned

theorem finish_hit {index : Nat} {a b : Byte} {actual : Word}
    (leftAt : (view input.value).left[index]? = some a)
    (rightAt : (view input.value).right[index]? = some b)
    (different : a ≠ b) (returned : returnValue actual = 0) :
    spec.result input.value actual := result_at_mismatch leftAt rightAt different returned

theorem return_replace (old : Word) (value : Byte) :
    returnValue (replaceLow8 old value) = value := (replaceLow8_widths old value).1

end EDSL.X86.VCGen.ByteEquality

namespace EDSL.X86.VCGen.ByteEquality
open Sequential

/-- Shared frame discharge after production block reduction. This is proof
composition over complete state fields, not a second interpreter. -/
macro "byte_equality_frame" frame:ident : tactic => `(tactic| (
  simp only [ByteEquality.commonFrame_iff, State.writeRegister,
    logicalFlags32_preserves, logicalFlags64_preserves, cmpFlags8_preserves,
    cmpFlags32_preserves, cmpFlags64_preserves, addFlags64_preserves,
    incFlags64_preserves, ($frame).memory, ($frame).flags, true_and, and_true]
  intro register notRax notRcx notR8
  simpa only [notRax,notRcx,notR8,ite_false] using
    ($frame).registers register notRax notRcx notR8))

macro "byte_equality_return" frame:ident correct:ident : tactic => `(tactic| (
  refine ⟨?_,rfl,rfl,rfl,?_,?_⟩
  · simpa [BufferCall.Spec.scalarSpec] using $correct
  · intro register saved
    have different := ByteEquality.saved_different register saved
    simpa only [State.writeRegister,different.1,different.2.1,different.2.2.1,
      different.2.2.2,ite_false] using
      ($frame).registers register different.2.1 different.2.2.1 different.2.2.2
  · simpa only [logicalFlags32_preserves,logicalFlags64_preserves,cmpFlags8_preserves,
      cmpFlags32_preserves,cmpFlags64_preserves,addFlags64_preserves,
      incFlags64_preserves] using ($frame).flags))

end EDSL.X86.VCGen.ByteEquality
