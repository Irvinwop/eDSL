/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.X86.VCGen.Frame
import EDSL.X86.VCGen.Artifact
import EDSL.ELF.Loader
import EDSL.Audit

namespace EDSL.Tests.VCGenReflection
open X86 Sequential VCGen

/- Exercise the executable decision procedure itself. The synthetic binary
zeroes a NONZERO accumulator and returns. Requiring a fixed AF is false, even
though either one particular AF stream can satisfy that requirement. -/
def bytes : List Byte := [0x31, 0xc0, 0xc3]
def graph : CFG.Graph := CFG.annotate
  [⟨0, .xorSelf32 .rax, false, 0⟩, ⟨2, .legacy .ret, false, 0⟩]
def entry : graph.Index := ⟨0, by decide⟩

def memory : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4099 then
    bytes[address.toNat - 4096]? else some 0
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4099)

def initial : State := ⟨fun register => if register = .rax then 0xffffffffffffffff else 0,
  4096, 0x202, memory⟩

def Allowed (_ : State) (read : Read) : Prop := read = ⟨.stack, 0, 8⟩

def Post (result : Result) : Prop := result.state.registers .rax = 0 ∧
  result.state.rip = 0 ∧ result.state.registers .rsp = 8 ∧
  result.instructions = 2 ∧ result.reads = [⟨.stack, 0, 8⟩]

instance (state : State) (read : Read) : Decidable (Allowed state read) :=
  inferInstanceAs (Decidable (_ = _))

instance (result : Result) : Decidable (Post result) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance : Decidable (wp graph 4096 Allowed 2 entry initial Post) :=
  decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 entry initial Post
    (fun _ => inferInstance)

/-- This uses the executable checker, then binds its evidence to real decoded
steps in actual RAM. A generator that skips the XOR, RET, stack read or exact
accounting cannot satisfy this independent contract. -/
theorem executable_accepts (choices : Choices) :
    ∃ result, Sequential.run choices 2 initial = .ok result ∧ Post result ∧
      result.state.memory = initial.memory ∧ result.instructions ≤ 2 ∧
      CheckedTrace Allowed choices initial result := by
  have accepted : certify bytes graph 4096 Allowed 2 entry initial Post = true := by decide
  exact certify_sound_frame accepted choices

def staleMemory : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4099 then
    (bytes.set 1 0xc9)[address.toNat - 4096]? else some 0
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4099)

def staleInitial : State := { initial with memory := staleMemory }

instance : Decidable (wp graph 4096 Allowed 2 entry staleInitial Post) :=
  decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 entry staleInitial Post
    (fun _ => inferInstance)

/-- A successful formula about the proposed XOR-EAX cannot certify actual RAM
containing XOR-ECX. This catches accidental omission of the actual-byte guard. -/
example : check graph 4096 Allowed 2 entry staleInitial Post = true ∧
    certify bytes graph 4096 Allowed 2 entry staleInitial Post = false := by decide

def FixedAF (result : Result) : Prop := result.state.flags.getLsbD 4 = false

instance (result : Result) : Decidable (FixedAF result) :=
  inferInstanceAs (Decidable (_ = _))

instance : Decidable (wp graph 4096 Allowed 2 entry initial FixedAF) :=
  decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 entry initial FixedAF
    (fun _ => inferInstance)

/-- Refuting the universal AF contract checks that reflection did not silently
choose just one execution's undefined flag. -/
example : check graph 4096 Allowed 2 entry initial FixedAF = false := by decide

def WrongCost (result : Result) : Prop := result.instructions = 1

instance (result : Result) : Decidable (WrongCost result) :=
  inferInstanceAs (Decidable (_ = _))

instance : Decidable (wp graph 4096 Allowed 2 entry initial WrongCost) :=
  decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 entry initial WrongCost
    (fun _ => inferInstance)

example : check graph 4096 Allowed 2 entry initial WrongCost = false := by decide

end EDSL.Tests.VCGenReflection

#audit_edsl
