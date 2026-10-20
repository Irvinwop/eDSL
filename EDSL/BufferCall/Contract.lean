/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.X86.Buffer

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.BufferCall
open X86 X86.Sequential

/-- Reuse scalar bindings; a byte binding leaves all upper 56 bits arbitrary. -/
inductive Argument where
  | scalar (binding : PureCall.Argument)
  | low8 (value : Byte)

abbrev Argument.word64 (value : Word) : Argument := .scalar (.word64 value)
abbrev Argument.low32 (value : BitVec 32) : Argument := .scalar (.low32 value)

def Argument.Holds : Argument → Word → Prop
  | .scalar binding, actual => binding.Holds actual
  | .low8 value, actual => actual.setWidth 8 = value

abbrev argumentRegister := PureCall.argumentRegister

/-- Initial mathematical snapshot at an actual base. Read-only descriptors may
alias whenever their byte observations are compatible in current memory. -/
structure Buffer where
  base : Word
  bytes : List Byte
  deriving DecidableEq, Repr

/-- Trusted registration fixes the input, snapshots, mathematics and usefulness.
No decoder, graph, rank, execution or desired machine state belongs in domain. -/
structure Spec where
  Input : Type
  arguments : Input → Fin 6 → Option Argument
  buffers : Input → List Buffer
  domain : Input → Prop
  result : Input → Word → Prop
  useful : Input → Prop

structure Invocation (spec : Spec) where
  value : spec.Input
  returnAddress : Word

def Bound (spec : Spec) (value : spec.Input) (state : State) : Prop :=
  ∀ index argument, spec.arguments value index = some argument →
    argument.Holds (state.registers (argumentRegister index))

/-- Present memory and arguments only. BufferAt includes nonwrapping bounds;
for an empty buffer it requires no read, canonicality, alignment or allocation.
The environmental CPU/OS assumptions are the sequential callable profile's. -/
structure Pre (spec : Spec) (bytes : List Byte)
    (input : Invocation spec) (initial : State) : Prop where
  domain : spec.domain input.value
  arguments : Bound spec input.value initial
  buffers : ∀ buffer ∈ spec.buffers input.value,
    BufferAt initial.memory buffer.base buffer.bytes
  code : CodeAt initial.memory initial.rip bytes
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

/-- Only the common scalar return/frame contract is reused through this view.
Arguments and snapshots remain fixed by BufferCall.Pre. -/
def Spec.scalarSpec (spec : Spec) : PureCall.Spec where
  Input := spec.Input
  arguments _ _ := none
  domain := spec.domain
  result := spec.result
  useful := spec.useful

abbrev calleeSaved := PureCall.calleeSaved

/-- Mathematical RAX return, complete RAM/permission equality, caller return,
RSP, SysV callee-saved GPRs, and every nonarithmetic flag. Result may select any
register view (e.g. low32 signed or low8) without constraining its upper bits. -/
abbrev Post (spec : Spec) (input : Invocation spec) (initial final : State) : Prop :=
  PureCall.Post spec.scalarSpec ⟨input.value, input.returnAddress⟩ initial final

/-- Natural, positive, fully contained span. No modular endpoint arithmetic or
alignment requirement; a zero-width operand never obtains buffer authority. -/
def Buffer.Contains (buffer : Buffer) (address : Word) (width : Nat) : Prop :=
  0 < width ∧ buffer.base.toNat ≤ address.toNat ∧
    address.toNat + width ≤ buffer.base.toNat + buffer.bytes.length

/-- All positive DATA widths are allowed when wholly inside one snapshot.
The executor independently determines which widths/instructions it supports. -/
def DataRead (buffers : List Buffer) (read : Read) : Prop :=
  read.kind = .data ∧ ∃ buffer ∈ buffers, buffer.Contains read.address read.bytes

/-- Original STACK8 or a positive complete DATA span in an initial buffer.
Changing RSP or reading equal bytes elsewhere creates no new authority. -/
def RawRead (spec : Spec) (input : Invocation spec) (initial : State) (read : Read) : Prop :=
  PureCall.RawRead initial read ∨ DataRead (spec.buffers input.value) read

/-- A proved execution policy, separate from present-only admission. Whole
memory equality retains all initial snapshots at every actual prefix. -/
def RawPolicy (spec : Spec) (input : Invocation spec) (initial : State) : Prop :=
  Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
    (fun _ read => RawRead spec input initial read)

theorem Buffer.empty (memory : Memory) (base : Word) : BufferAt memory base [] := by
  refine ⟨?_, ?_⟩
  · simp only [List.length_nil, Nat.add_zero]
    exact Nat.le_of_lt base.isLt
  · intro offset byte present
    simp at present

theorem Buffer.no_empty_span {base address : Word} {width : Nat} :
    ¬(Buffer.mk base []).Contains address width := by
  rintro ⟨positive, lower, upper⟩
  change base.toNat ≤ address.toNat at lower
  change address.toNat + width ≤ base.toNat + 0 at upper
  omega

theorem DataRead.no_empty {buffers : List Buffer}
    (empty : ∀ buffer ∈ buffers, buffer.bytes = []) (read : Read) : ¬DataRead buffers read := by
  rintro ⟨_, buffer, member, span⟩
  have zero := empty buffer member
  obtain ⟨base, bytes⟩ := buffer
  dsimp only at zero
  subst bytes
  exact Buffer.no_empty_span span

/-- Memory compatibility follows from actual byte reads, including overlapping
snapshots; disjointness is not required by the call contract. -/
theorem buffers_compatible {memory : Memory} {left right : Buffer}
    (a : BufferAt memory left.base left.bytes) (b : BufferAt memory right.base right.bytes)
    {i j : Nat} {x y : Byte} (atA : left.bytes[i]? = some x)
    (atB : right.bytes[j]? = some y)
    (same : left.base + BitVec.ofNat 64 i = right.base + BitVec.ofNat 64 j) : x = y := by
  have first := a.2 i x atA
  have second := b.2 j y atB
  rw [same] at first
  exact Except.ok.inj (first.symm.trans second)

end EDSL.BufferCall
