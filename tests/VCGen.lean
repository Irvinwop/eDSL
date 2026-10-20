/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Examples
import EDSL.Audit

namespace EDSL.Tests.VCGen
open X86 X86.Sequential X86.VCGen X86.VCGen.Examples

/-- Independent incompatible contracts cannot both obtain returning runs
from the shared checker, for ANY admitted initial state and AF stream. -/
private theorem incompatible_rejected (routine : Routine) (initial : State)
    (returnAddress payload : Word)
    (code : CodeAt initial.memory initial.rip (bytes routine))
    (ready : ReturnReady initial returnAddress)
    (data : DataReady routine initial payload) (order : OrderReady routine initial)
    (Wrong : Result → Prop)
    (incompatible : ∀ result, Post routine initial returnAddress payload result → ¬Wrong result) :
    ¬wp (graph routine) initial.rip (Allowed routine initial) (cost routine)
      (entry routine) initial Wrong := by
  intro vc
  let choices : Choices := fun _ => false
  obtain ⟨correct,actual,post,_⟩ := verifies routine initial returnAddress payload
    code ready data order choices
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((graph routine).node (entry routine)).offset := by simp
  obtain ⟨incorrect,claimed,wrong,_,_⟩ := X86.VCGen.run_sound (valid routine) code pc vc choices
  have same : incorrect = correct := Except.ok.inj (claimed.symm.trans actual)
  subst incorrect
  exact incompatible correct post wrong

-- A plausible off-by-one/wrong-register value contract is rejected, with
-- symbolic incoming registers, flags and RAM rather than a chosen fixture.
theorem wrong_identity_value (initial : State) (returnAddress wrong : Word)
    (code : CodeAt initial.memory initial.rip (bytes .identity64))
    (ready : ReturnReady initial returnAddress) (different : wrong ≠ initial.registers .rdi) :
    ¬wp (graph .identity64) initial.rip (Allowed .identity64 initial) 2
      (entry .identity64) initial (fun result => result.state.registers .rax = wrong) := by
  apply incompatible_rejected .identity64 initial returnAddress 0 code ready
    (by simp [DataReady]) (by simp [OrderReady])
  intro result post claimed
  have returned : result.state.registers .rax = initial.registers .rdi := post.1
  exact different (claimed.symm.trans returned)

-- Exact cost is an observable contract, not merely a sufficient fuel bound.
theorem wrong_cost (routine : Routine) (initial : State) (returnAddress payload : Word)
    (code : CodeAt initial.memory initial.rip (bytes routine))
    (ready : ReturnReady initial returnAddress)
    (data : DataReady routine initial payload) (order : OrderReady routine initial)
    (claimedCost : Nat) (different : claimedCost ≠ cost routine) :
    ¬wp (graph routine) initial.rip (Allowed routine initial) (cost routine)
      (entry routine) initial (fun result => result.instructions = claimedCost) := by
  apply incompatible_rejected routine initial returnAddress payload code ready data order
  intro result post claimed
  exact different (claimed.symm.trans post.2.2.2.2.2.2.1)

-- A successful LOAD+RET cannot promise a trace that omits the data operand.
theorem omitted_data_read (initial : State) (returnAddress payload : Word)
    (code : CodeAt initial.memory initial.rip (bytes .load64))
    (ready : ReturnReady initial returnAddress)
    (loaded : loadQWord initial.memory (initial.registers .rdi) = .ok payload) :
    ¬wp (graph .load64) initial.rip (Allowed .load64 initial) 2
      (entry .load64) initial (fun result => result.reads = [stackRead initial]) := by
  apply incompatible_rejected .load64 initial returnAddress payload code ready
    (by simpa [DataReady] using loaded) (by simp [OrderReady])
  intro result post claimed
  have exactReads := post.2.2.2.2.2.2.2
  rw [claimed] at exactReads
  have lengths := congrArg List.length exactReads
  simp [footprint] at lengths

/-- Permissions apply to actual observations in the trace. This induction
does not assume that successful machine reads imply permission. -/
private theorem trace_reads {Permit : Read → Prop} {choices initial result}
    (trace : CheckedTrace (fun _ read => Permit read) choices initial result) :
    ∀ read ∈ result.reads, Permit read := by
  induction trace with
  | ret _ allowed => exact allowed
  | @next choices initial middle reads result _ allowed _ induction =>
    intro read member
    change read ∈ reads ++ result.reads at member
    rcases List.mem_append.mp member with headMember | suffix
    · exact allowed read headMember
    · exact induction read suffix

-- All physical memory accesses can succeed while the independent policy
-- denies the data loan. The generator must reject that policy.
theorem denied_data_permission (initial : State) (returnAddress payload : Word)
    (code : CodeAt initial.memory initial.rip (bytes .load64))
    (ready : ReturnReady initial returnAddress)
    (loaded : loadQWord initial.memory (initial.registers .rdi) = .ok payload) :
    ¬wp (graph .load64) initial.rip (fun _ read => read = stackRead initial) 2
      (entry .load64) initial (fun _ => True) := by
  intro vc
  let choices : Choices := fun _ => false
  obtain ⟨correct,actual,post,_⟩ := verifies .load64 initial returnAddress payload code ready
    (by simpa [DataReady] using loaded) (by simp [OrderReady]) choices
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((graph .load64).node (entry .load64)).offset := by simp
  obtain ⟨incorrect,claimed,_,_,trace⟩ := X86.VCGen.run_sound (valid .load64) code pc vc choices
  have same : incorrect = correct := Except.ok.inj (claimed.symm.trans actual)
  subst incorrect
  have allowed := trace_reads trace (dataRead initial) (by
    rw [post.2.2.2.2.2.2.2]
    simp [footprint])
  cases allowed

-- Mutating MOV RAX,RDI into the same-length MOV RAX,RSI cannot keep its CFG
-- certificate. This exercises exact decoder/byte binding, not graph assignment.
example : CFG.check ((bytes .identity64).set 2 0xf0) (graph .identity64) = false := by decide

-- Truncation may not obtain the original graph's RET/closed-edge guarantees.
example : CFG.check ((bytes .identity64).take 3) (graph .identity64) = false := by decide

-- ENDBR32 remains outside the exact ENDBR64 subset. A similar prefix must
-- not be stripped or accepted as the supported landing-pad encoding.
example : CFG.discover ([0xf3,0x0f,0x1e,0xfb] ++ bytes .identity64) = none := by decide

-- The next instruction consumes the last unit of fuel; RET cannot then run.
theorem insufficient_fuel (initial : State) (base : Word) :
    ¬wp (graph .identity64) base (fun _ _ => True) 1 (entry .identity64)
      initial (fun _ => True) := by
  have instruction : ((graph .identity64).node (entry .identity64)).instruction =
      .movReg64 .rax .rdi := rfl
  simp [wp,instruction,Sequential.execute,
    Sequential.Instruction.operandReads]

-- An accessible caller slot containing a noncanonical target is insufficient:
-- the production RET check fails regardless of the independent policy/Post.
theorem noncanonical_return (initial : State) (base target : Word)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (badTarget : canonical target = false) (Permit : State → Read → Prop)
    (fuel : Nat) (Claim : Result → Prop) :
    ¬wp (graph .identity64) base Permit (fuel + 1) ⟨1,by decide⟩ initial Claim := by
  have instruction : ((graph .identity64).node ⟨1,by decide⟩).instruction = .legacy .ret := rfl
  simp [wp,instruction,Sequential.execute,X86.executeInstruction,executeRet,stack,badTarget]

-- Read failure is an execution failure, even when every read is authorized.
theorem inaccessible_load (initial : State) (base : Word) (fault : Error)
    (failed : loadQWord initial.memory (initial.registers .rdi) = .error fault)
    (Permit : State → Read → Prop) (fuel : Nat) (Claim : Result → Prop) :
    ¬wp (graph .load64) base Permit (fuel + 1) (entry .load64) initial Claim := by
  have instruction : ((graph .load64).node (entry .load64)).instruction =
      .loadMem64 .rax (.base .rdi) := rfl
  simp [wp,instruction,Sequential.execute,Address.eval,failed]

theorem inaccessible_return_stack (initial : State) (base : Word) (fault : Error)
    (failed : readWord initial.memory (initial.registers .rsp) = .error fault)
    (Permit : State → Read → Prop) (fuel : Nat) (Claim : Result → Prop) :
    ¬wp (graph .identity64) base Permit (fuel + 1) ⟨1,by decide⟩ initial Claim := by
  have instruction : ((graph .identity64).node ⟨1,by decide⟩).instruction = .legacy .ret := rfl
  simp [wp,instruction,Sequential.execute,X86.executeInstruction,executeRet,failed]

end EDSL.Tests.VCGen

#print axioms EDSL.X86.VCGen.Examples.generated_vc
#print axioms EDSL.X86.VCGen.Examples.verifies
#print axioms EDSL.Tests.VCGen.wrong_identity_value
#print axioms EDSL.Tests.VCGen.wrong_cost
#print axioms EDSL.Tests.VCGen.omitted_data_read
#print axioms EDSL.Tests.VCGen.denied_data_permission

#audit_edsl
