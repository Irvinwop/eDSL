/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.BufferCall
import EDSL.Grading.BufferTask

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.IndexSearch
open Sequential
open Grading.IndexSearch

/-- The two registered element widths; neither selects a candidate contract. -/
inductive Width where
  | byte | u32
  deriving DecidableEq, Repr

def bits : Width → Nat | .byte => 8 | .u32 => 32
abbrev Element (width : Width) := BitVec (bits width)
def stride : Width → Nat | .byte => 1 | .u32 => 4
def scale : Width → Fin 4 | .byte => 0 | .u32 => 2

def taskID : Width → Grading.BufferTask.TaskID
  | .byte => .memchrIndex | .u32 => .linearSearchU32

def spec : Width → BufferCall.Spec | .byte => byteSpec | .u32 => u32Spec

theorem registered_spec (width : Width) :
    Grading.BufferTask.registeredSpec (taskID width) = spec width := by cases width <;> rfl

def view (width : Width) : (spec width).Input → Input (Element width) :=
  match width with | .byte => id | .u32 => id

def values (width : Width) (input : (spec width).Input) : List (Element width) :=
  (view width input).values

def base (width : Width) (input : (spec width).Input) : Word := (view width input).base
def key (width : Width) (input : (spec width).Input) : Element width := (view width input).key

theorem result_iff (width : Width) (input : (spec width).Input) (actual : Word) :
    (spec width).result input actual ↔ Result (values width input) (key width input) actual := by
  cases width <;> rfl

/-- Both layouts use RAX/RCX as scratch. RDX, including its unused high bits,
all other registers, complete RAM/permissions and nonarithmetic flags survive. -/
structure CommonFrame (initial state : State) : Prop where
  memory : state.memory = initial.memory
  registers : ∀ register, register ≠ .rax → register ≠ .rcx →
    state.registers register = initial.registers register
  flags : state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem commonFrame_iff (initial state : State) : CommonFrame initial state ↔
    state.memory = initial.memory ∧
    (∀ register, register ≠ .rax → register ≠ .rcx →
      state.registers register = initial.registers register) ∧
    state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask :=
  ⟨fun f => ⟨f.memory, f.registers, f.flags⟩, fun ⟨m, r, f⟩ => ⟨m, r, f⟩⟩

theorem CommonFrame.refl (initial : State) : CommonFrame initial initial :=
  ⟨rfl, fun _ _ _ => rfl, rfl⟩

theorem CommonFrame.rsp {initial state : State} (f : CommonFrame initial state) :
    state.registers .rsp = initial.registers .rsp := f.registers .rsp (by decide) (by decide)
theorem CommonFrame.rdi {initial state : State} (f : CommonFrame initial state) :
    state.registers .rdi = initial.registers .rdi := f.registers .rdi (by decide) (by decide)
theorem CommonFrame.rsi {initial state : State} (f : CommonFrame initial state) :
    state.registers .rsi = initial.registers .rsi := f.registers .rsi (by decide) (by decide)
theorem CommonFrame.rdx {initial state : State} (f : CommonFrame initial state) :
    state.registers .rdx = initial.registers .rdx := f.registers .rdx (by decide) (by decide)

theorem saved_different (register : Register) (saved : register ∈ PureCall.calleeSaved) :
    register ≠ .rsp ∧ register ≠ .rax ∧ register ≠ .rcx := by
  simp only [PureCall.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

variable {width : Width} {bytes : List Byte} {input : BufferCall.Invocation (spec width)}
  {initial state : State}

theorem count_small (pre : BufferCall.Pre (spec width) bytes input initial) :
    (values width input.value).length < 2^64 := by cases width <;> exact pre.domain

theorem count_nat (pre : BufferCall.Pre (spec width) bytes input initial) :
    (BitVec.ofNat 64 (values width input.value).length).toNat = (values width input.value).length := by
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (count_small pre)]

theorem base_argument (pre : BufferCall.Pre (spec width) bytes input initial) :
    initial.registers .rdi = base width input.value := by
  cases width <;> exact pre.arguments 0 (.word64 _) rfl

theorem count_argument (pre : BufferCall.Pre (spec width) bytes input initial) :
    initial.registers .rsi = BitVec.ofNat 64 (values width input.value).length := by
  cases width <;> exact pre.arguments 1 (.word64 _) rfl

theorem key_argument (pre : BufferCall.Pre (spec width) bytes input initial) :
    (initial.registers .rdx).setWidth (bits width) = key width input.value := by
  cases width with
  | byte => exact pre.arguments 2 (.low8 _) rfl
  | u32 => exact pre.arguments 2 (.low32 _) rfl

/-- One production comparison, without exposing its width in the loop proof. -/
def comparison (width : Width) (cursor : Register) : Sequential.Instruction :=
  match width with
  | .byte => .cmpMemReg8 (.indexed .rdi cursor 0) .rdx
  | .u32 => .cmpMemReg32 (.indexed .rdi cursor 2) .rdx

def comparisonFlags (width : Width) (old : Word) (value needle : Element width) : Word :=
  match width with
  | .byte => cmpFlags8 old value needle
  | .u32 => cmpFlags32 old value needle

theorem comparisonFlags_zero (width : Width) (old : Word) (value needle : Element width) :
    (comparisonFlags width old value needle).getLsbD 6 = (value == needle) := by
  cases width
  · exact cmpFlags8_zero old value needle
  · exact cmpFlags32_zero old value needle

theorem comparisonFlags_preserves (width : Width) (old : Word) (value needle : Element width) :
    comparisonFlags width old value needle &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask := by
  cases width
  · exact cmpFlags8_preserves old value needle
  · exact cmpFlags32_preserves old value needle

/-- SIB scaling and the independent snapshot use the same modular address.
The snapshot's positive span separately proves that actual reads cannot wrap. -/
theorem scaled_index (width : Width) (index : Word) :
    index <<< (scale width).val = BitVec.ofNat 64 (stride width * index.toNat) := by
  cases width
  · simp [scale, stride]
  · change index <<< 2 = BitVec.ofNat 64 (4 * index.toNat)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mul_comm index.toNat]

/-- Actual snapshot reads, full DATA1/DATA4 footprints and key truncation are
proved once. No alignment, alias exclusion, future execution or count cap is
required. Both AF values use this same production execute operation. -/
theorem read_comparison (pre : BufferCall.Pre (spec width) bytes input initial)
    (frame : CommonFrame initial state) (cursor : Register)
    (inside : (state.registers cursor).toNat < (values width input.value).length) :
    ∃ value, (values width input.value)[(state.registers cursor).toNat]? = some value ∧
      BufferCall.RawRead (spec width) input initial
        ⟨.data, (.indexed .rdi cursor (scale width) : Address).eval state, stride width⟩ ∧
      ∀ af, execute state (comparison width cursor) af =
        .ok ⟨.next { state with
          rip := state.rip + 3
          flags := comparisonFlags width state.flags value (key width input.value) },
          [⟨.data, (.indexed .rdi cursor (scale width) : Address).eval state, stride width⟩]⟩ := by
  have present := List.getElem?_eq_getElem inside
  have rdi := frame.rdi.trans (base_argument pre)
  have rdx := congrArg (BitVec.setWidth (bits width)) frame.rdx
  have needle := rdx.trans (key_argument pre)
  have address : (.indexed .rdi cursor (scale width) : Address).eval state =
      base width input.value + BitVec.ofNat 64 (stride width * (state.registers cursor).toNat) := by
    simp only [Address.eval, rdi, scaled_index]
  cases width with
  | byte =>
    obtain ⟨loaded, allowed⟩ := byte_read pre present
    rw [← frame.memory] at loaded
    have byteAddress : (.indexed .rdi cursor (scale .byte) : Address).eval state =
        input.value.base + BitVec.ofNat 64 (state.registers cursor).toNat := by
      simpa only [stride, Nat.one_mul, base, view, id_eq] using address
    change (Address.indexed .rdi cursor 0).eval state = _ at byteAddress
    change (state.registers .rdx).setWidth 8 = input.value.key at needle
    refine ⟨_, present, ?_, ?_⟩
    · simpa only [scale, byteAddress, spec, stride] using allowed
    · intro af
      simp only [comparison, execute_cmpMemReg8, byteAddress, loaded, needle, comparisonFlags, key, view, id_eq,
        Sequential.Instruction.length, scale, stride, pure_ok]
      rfl
  | u32 =>
    obtain ⟨loaded, allowed⟩ := u32_read pre present
    rw [← frame.memory] at loaded
    have wordAddress : (.indexed .rdi cursor (scale .u32) : Address).eval state =
        input.value.base + BitVec.ofNat 64 (4 * (state.registers cursor).toNat) := address
    change (Address.indexed .rdi cursor 2).eval state = _ at wordAddress
    change (state.registers .rdx).setWidth 32 = input.value.key at needle
    refine ⟨_, present, ?_, ?_⟩
    · simpa only [scale, wordAddress, spec, stride] using allowed
    · intro af
      simp only [comparison, execute_cmpMemReg32, wordAddress, loaded, needle, comparisonFlags, key, view, id_eq,
        Sequential.Instruction.length, scale, stride, pure_ok]
      rfl

/-- Full-width increment cannot wrap before the admitted count. -/
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

theorem advance {index : Word} {value : Element width}
    (pre : BufferCall.Pre (spec width) bytes input initial)
    (inside : index.toNat < (values width input.value).length)
    (scanned : Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value)) index.toNat)
    (present : (values width input.value)[index.toNat]? = some value)
    (miss : value ≠ key width input.value) :
    Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value)) (index + 1).toNat := by
  rw [next_nat (count_small pre) inside]
  exact scanned.advance present (by simp [equals, miss])

theorem finish_hit {index : Word}
    (scanned : Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value)) index.toNat)
    (present : (values width input.value)[index.toNat]? = some (key width input.value)) :
    (spec width).result input.value index := by
  apply (result_iff width input.value index).mpr
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Result.of_hit scanned present

theorem finish_bound {index : Nat}
    (scanned : Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value)) index)
    (done : index = (values width input.value).length) :
    (spec width).result input.value sizeMax := by
  apply (result_iff width input.value sizeMax).mpr
  exact ⟨index, scanned.finish_bound done, by simp [encode, done]⟩

/-- Compose a production next-step equality into the generated WP without
unfolding a width-parametric instruction. This is only a WP proof rule. -/
theorem wp_next {graph : CFG.Graph} {codeBase : Word} {Post : State → Prop}
    {AllowedRead : State → Read → Prop} {Inv : graph.Index → State → Prop}
    {rank : graph.Index → State → Nat} {budget fuel : Nat} {node : graph.Index}
    {before after : State} {reads : List Read}
    (effect : ∀ af, execute before (graph.node node).instruction af = .ok ⟨.next after, reads⟩)
    (allowed : ∀ read ∈ reads, AllowedRead before read) (destination : graph.Index)
    (pc : after.rip = codeBase + BitVec.ofNat 64 (graph.node destination).offset)
    (continuation : if graph.cutpoint destination then
      Inv destination after ∧ rank destination after < budget
      else Cutpoints.wp graph codeBase Post AllowedRead Inv rank budget fuel destination after) :
    Cutpoints.wp graph codeBase Post AllowedRead Inv rank budget (fuel + 1) node before := by
  rw [Cutpoints.wp]
  intro af
  rw [effect]
  exact ⟨allowed, destination, pc, continuation⟩


end EDSL.X86.VCGen.IndexSearch
