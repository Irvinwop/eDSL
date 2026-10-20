/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core

namespace EDSL.X86.VCGen.Artifact
open Sequential

variable {profile : CFG.Profile}

/-- Bind a selected complete machine-code window to literal bytes of the final
artifact. This performs no ELF parsing or source-language interpretation. -/
def checkWindow (file : List Byte) (offset : Nat) (bytes : List Byte) : Bool :=
  decide (offset + bytes.length ≤ file.length) &&
    (List.range bytes.length).all fun index =>
      decide (file[offset + index]? = bytes[index]?)

theorem checked_window_byte {file bytes : List Byte} {offset : Nat}
    (checked : checkWindow file offset bytes = true) {index : Nat} {byte : Byte}
    (present : bytes[index]? = some byte) : file[offset + index]? = some byte := by
  have inside := (List.getElem_of_getElem? present).1
  have atIndex := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 index
    (List.mem_range.mpr inside)
  exact (of_decide_eq_true atIndex).trans present

/-- Explicit environment contract: the selected final-file interval is mapped
at the current executable address, with no address wrap. This can be provided
by an independently verified loader, OS admission, or a declared runtime
mapping assumption. It does not assert that a general ELF parser is verified. -/
def MappedWindow (memory : Memory) (base : Word) (file : List Byte)
    (offset length : Nat) : Prop :=
  base.toNat + length ≤ 2^64 ∧
  ∀ index byte, index < length → file[offset + index]? = some byte →
    fetchByte memory (base + BitVec.ofNat 64 index) = .ok byte

theorem codeAt {file bytes : List Byte} {offset : Nat} {memory : Memory} {base : Word}
    (checked : checkWindow file offset bytes = true)
    (mapped : MappedWindow memory base file offset bytes.length) :
    CodeAt memory base bytes := by
  refine ⟨mapped.1, ?_⟩
  intro index byte present
  exact mapped.2 index byte (List.getElem_of_getElem? present).1
    (checked_window_byte checked present)

/-- One reusable bridge from exact final artifact bytes and explicit executable
mapping to every generated bounded functional, footprint and cost theorem.
No symbol extractor or disassembler is in the proof's trusted path. -/
theorem sound {file bytes : List Byte} {offset : Nat} {graph : CFG.Graph}
    (window : checkWindow file offset bytes = true) (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (mapped : MappedWindow initial.memory base file offset bytes.length)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTrace AllowedRead choices initial result :=
  run_sound valid (codeAt window mapped) pc vc choices

end EDSL.X86.VCGen.Artifact
