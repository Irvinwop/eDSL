/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.BufferCall
import Lean

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.BufferCallVCGen
open X86 X86.Sequential

/-- Synthetic routine: return zero without touching RDI when RCX is zero;
otherwise repeatedly read the same qword, returning its value after RCX
iterations. TEST introduces both AF choices; LOOP does not consult its ZF.
The count ranges over the full Word domain, independently of code size. -/
def bytes : List Byte :=
  [0x48, 0x89, 0xc8, 0xe3, 0x08, 0x48, 0x8b, 0x07,
   0x48, 0x85, 0xc0, 0xe2, 0xf8, 0xc3]

abbrev graph : CFG.Graph := ⟨[
  ⟨0, .movReg64 .rax .rcx, true, 2⟩,
  ⟨3, .legacy (.jrcxz 8), false, 1⟩,
  ⟨5, .loadMem64 .rax (.base .rdi), true, 3⟩,
  ⟨8, .test64 .rax .rax, false, 2⟩,
  ⟨11, .legacy (.loopRcx 248), false, 1⟩,
  ⟨13, .legacy .ret, false, 0⟩], 3⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide)

abbrev entry : graph.Index := ⟨0, by decide⟩
abbrev loop : graph.Index := ⟨2, by decide⟩

structure Input where
  base : Word
  count : Word
  value : Word

def encoded (value : Word) : List Byte :=
  [value.extractLsb' 0 8, value.extractLsb' 8 8,
   value.extractLsb' 16 8, value.extractLsb' 24 8,
   value.extractLsb' 32 8, value.extractLsb' 40 8,
   value.extractLsb' 48 8, value.extractLsb' 56 8]

/-- Independent mathematical contract; the count-zero case has no data span.
No executable semantics, graph, fuel or future state occurs in the domain. -/
def spec : BufferCall.Spec where
  Input := Input
  arguments input index :=
    match index.val with
    | 0 => some (.word64 input.base)
    | 3 => some (.word64 input.count)
    | _ => none
  buffers input := if input.count = 0 then [] else [⟨input.base, encoded input.value⟩]
  domain _ := True
  result input result := result = if input.count = 0 then 0 else input.value
  useful _ := True

private theorem snapshot_load {memory : Memory} {base value : Word}
    (snapshot : BufferAt memory base (encoded value)) :
    loadQWord memory base = .ok value := by
  have bound : ¬base.toNat + 7 ≥ 2^64 := by
    have size := snapshot.1
    simp only [encoded, List.length_cons, List.length_nil] at size
    omega
  have at0 : readDataByte memory base = .ok (value.extractLsb' 0 8) := by
    simpa using snapshot.2 0 _ (by rfl)
  have at1 := snapshot.2 1 _ (by rfl)
  have at2 := snapshot.2 2 _ (by rfl)
  have at3 := snapshot.2 3 _ (by rfl)
  have at4 := snapshot.2 4 _ (by rfl)
  have at5 := snapshot.2 5 _ (by rfl)
  have at6 := snapshot.2 6 _ (by rfl)
  have at7 := snapshot.2 7 _ (by rfl)
  simp only [BitVec.ofNat_eq_ofNat, loadQWord, bound, ↓reduceIte, at0, at1, at2, at3, at4, at5, at6, at7,
    ok_bind, pure_ok, qword_join_extracts]

def Frame (initial state : State) : Prop :=
  state.memory = initial.memory ∧
  (∀ register, register ≠ .rax → register ≠ .rcx →
    state.registers register = initial.registers register) ∧
  state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

def Inv (input : BufferCall.Invocation spec) (initial : State)
    (node : graph.Index) (state : State) : Prop :=
  Frame initial state ∧
    if node.val = 0 then state.registers .rcx = input.value.count
    else input.value.count ≠ 0 ∧ state.registers .rcx ≠ 0

def rank (node : graph.Index) (state : State) : Nat :=
  (state.registers .rcx).toNat + if node.val = 0 then 1 else 0

local macro "block_successor_at" index:num : tactic => `(tactic|
  refine ⟨⟨$index:num, by decide⟩, by decide, ?_⟩)

local macro "block_successor" : tactic => `(tactic|
  first
  | block_successor_at 0
  | block_successor_at 1
  | block_successor_at 2
  | block_successor_at 3
  | block_successor_at 4
  | block_successor_at 5)

/-- The only client assertions are at entry and the load/loop header. Reducing
one generated block proves all its instruction obligations for arbitrary
registers, flags, current RAM, relocation base and AF choices. -/
def annotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) :
    VCGen.Cutpoints.Annotations bytes graph initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) where
  Inv := Inv input initial
  rank := rank
  blocks cut state isCut binding admitted := by
    have cuts : cut = entry ∨ cut = loop := by
      have allCuts : ∀ node : graph.Index,
          graph.cutpoint node = true → node = entry ∨ node = loop := by decide
      exact allCuts cut isCut
    obtain ⟨⟨memory, registers, flags⟩, counter⟩ := admitted
    have rsp := registers .rsp (by decide) (by decide)
    have rdi := registers .rdi (by decide) (by decide)
    have base : initial.registers .rdi = input.value.base :=
      pre.arguments 0 (.word64 input.value.base) rfl
    have stack : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
      simpa only [memory, rsp] using pre.stack
    have readAllowed : BufferCall.RawRead spec input initial
        ⟨.stack, state.registers .rsp, 8⟩ := .inl ⟨rfl, rsp, rfl⟩
    have canonicalRet : canonical (initial.rip + 13#64) = true := by
      simpa [CFG.Graph.node, graph]
        using valid.canonical_node binding.1 (⟨5, by decide⟩ : graph.Index)
    have canonicalLoop : canonical (initial.rip + 5#64) = true := by
      simpa [CFG.Graph.node, graph]
        using valid.canonical_node binding.1 loop
    rcases cuts with same | same
    · subst cut
      change state.registers .rcx = input.value.count at counter
      have pc : state.rip = initial.rip := by
        simpa only [CFG.Graph.node, graph, entry, List.getElem_cons_zero,
          BitVec.add_zero] using binding.2
      by_cases zero : input.value.count = 0#64
      · change VCGen.Cutpoints.wp graph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (Inv input initial) rank (rank entry state) 3 entry state
        repeat' (
          rw [VCGen.Cutpoints.wp]
          intro af
          simp only [CFG.Graph.node, graph, entry, execute, Instruction.operandReads,
            executeInstruction, executeJrcxz, executeShortBranch, executeRet,
            State.writeRegister, pure_ok]
          simp [pc, memory, rsp, pre.stack, pre.returnCanonical, counter, zero,
            canonicalRet, BitVec.add_assoc]
          first | block_successor | skip
          try simp only [CFG.Graph.cutpoint, CFG.Graph.node,
            List.getElem_cons_zero, List.getElem_cons_succ])
        constructor
        · exact .inl ⟨rfl, rfl, rfl⟩
        · refine ⟨?_, rfl, rfl, rfl, ?_, flags⟩
          · simp [BufferCall.Spec.scalarSpec, spec, zero]
          · intro register saved
            have different : register ≠ .rsp ∧ register ≠ .rax ∧ register ≠ .rcx := by
              simp only [PureCall.calleeSaved,
                List.mem_cons, List.not_mem_nil, or_false] at saved
              rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
            simpa only [different.1, different.2.1, ite_false] using
              registers register different.2.1 different.2.2
      · change VCGen.Cutpoints.wp graph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (Inv input initial) rank (rank entry state) 3 entry state
        repeat' (
          rw [VCGen.Cutpoints.wp]
          intro af
          simp only [CFG.Graph.node, graph, entry, execute, Instruction.operandReads,
            executeInstruction, executeJrcxz, executeShortBranch, State.writeRegister, pure_ok]
          simp [pc, memory, counter, zero, BitVec.add_assoc]
          first | block_successor | skip
          try simp only [CFG.Graph.cutpoint, CFG.Graph.node,
            List.getElem_cons_zero, List.getElem_cons_succ])
        simp [Inv, Frame, rank, flags, counter, zero]
        intro register notRax notRcx
        simpa only [notRax, ite_false] using registers register notRax notRcx
    · subst cut
      change input.value.count ≠ 0#64 ∧ state.registers .rcx ≠ 0#64 at counter
      have pc : state.rip = initial.rip + 5#64 := by
        simpa [CFG.Graph.node, graph, loop] using binding.2
      have snapshot : BufferAt initial.memory input.value.base (encoded input.value.value) :=
        pre.buffers ⟨input.value.base, encoded input.value.value⟩ (by simp [spec, counter.1])
      have loaded : loadQWord initial.memory (initial.registers .rdi) = .ok input.value.value := by
        rw [base]
        exact snapshot_load snapshot
      have dataAllowed : BufferCall.RawRead spec input initial
          ⟨.data, initial.registers .rdi, 8⟩ := by
        apply Or.inr
        refine ⟨rfl, ⟨input.value.base, encoded input.value.value⟩,
          by simp [spec, counter.1], ?_⟩
        simp [BufferCall.Buffer.Contains, base, encoded]
      have decreased : (state.registers .rcx - 1).toNat < (state.registers .rcx).toNat := by
        have positive : 0 < (state.registers .rcx).toNat := by
          have naturalNonzero : (state.registers .rcx).toNat ≠ 0 := by
            intro zero
            apply counter.2
            apply BitVec.eq_of_toNat_eq
            simpa using zero
          omega
        have oneLe : (1 : Word) ≤ state.registers .rcx := by
          change 1 ≤ (state.registers .rcx).toNat
          omega
        rw [BitVec.toNat_sub_of_le oneLe]
        change (state.registers .rcx).toNat - 1 < (state.registers .rcx).toNat
        omega
      by_cases last : state.registers .rcx - 1#64 = 0#64
      · change VCGen.Cutpoints.wp graph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (Inv input initial) rank (rank loop state) 4 loop state
        repeat' (
          rw [VCGen.Cutpoints.wp]
          intro af
          simp only [CFG.Graph.node, graph, loop, execute, Instruction.operandReads,
            Address.eval, Instruction.length, executeInstruction, executeLoop, executeShortBranch, executeRet,
            State.writeRegister, pure_ok]
          simp [pc, memory, rsp, rdi, loaded, pre.stack, pre.returnCanonical, last,
            dataAllowed, BitVec.add_assoc]
          first | block_successor | skip
          try simp only [CFG.Graph.cutpoint, CFG.Graph.node,
            List.getElem_cons_zero, List.getElem_cons_succ])
        constructor
        · exact .inl ⟨rfl, rfl, rfl⟩
        · refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
          · simp [BufferCall.Spec.scalarSpec, spec, counter.1]
          · intro register saved
            have different : register ≠ .rsp ∧ register ≠ .rax ∧ register ≠ .rcx := by
              simp only [PureCall.calleeSaved,
                List.mem_cons, List.not_mem_nil, or_false] at saved
              rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
            simpa only [different.1, different.2.1, different.2.2, ite_false] using
              registers register different.2.1 different.2.2
          · exact (logicalFlags64_preserves _ _ _).trans flags
      · change VCGen.Cutpoints.wp graph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (Inv input initial) rank (rank loop state) 4 loop state
        have condition : state.registers .rcx - (1#64) ≠ (0#64) := last
        repeat' (
          rw [VCGen.Cutpoints.wp]
          intro af
          simp only [CFG.Graph.node, graph, loop, execute, Instruction.operandReads,
            Address.eval, Instruction.length, executeInstruction, executeLoop, executeShortBranch,
            State.writeRegister, pure_ok]
          simp [pc, memory, rdi, loaded, condition, dataAllowed, canonicalLoop, BitVec.add_assoc]
          first | block_successor | skip
          try simp only [CFG.Graph.cutpoint, CFG.Graph.node,
            List.getElem_cons_zero, List.getElem_cons_succ])
        simp [Inv, Frame, rank, flags, logicalFlags64_preserves, counter.1, condition]
        constructor
        · intro register notRax notRcx
          simpa only [notRax, notRcx, ite_false] using registers register notRax notRcx
        · simpa [BitVec.toNat_sub] using decreased


private theorem entry_invariant (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) :
    (annotations input initial pre).Inv valid.entry initial := by
  change Frame initial initial ∧ initial.registers .rcx = input.value.count
  exact ⟨⟨rfl, fun _ _ _ => rfl, rfl⟩,
    pre.arguments 3 (.word64 input.value.count) rfl⟩

theorem generated (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) :
    ∃ evidence : VCGen.Cutpoints.Annotations bytes graph initial.rip
        (BufferCall.Post spec input initial)
        (fun _ read => BufferCall.RawRead spec input initial read),
      evidence.Inv valid.entry initial :=
  ⟨annotations input initial pre, entry_invariant input initial pre⟩

/-- Exercises the final adapter, including its resource and prefix-policy
conclusions, for a synthetic buffer call with arbitrary dynamic count. -/
theorem semantics : Grading.ReadOnlySemanticClaim (BufferCall.readOnlyTask spec) bytes :=
  VCGen.bufferCall_semantics_of_cutpoints spec bytes graph valid generated

/-- The evaluator fuel is obtained from the input-dependent rank, with no
small-count restriction and no iteration over the input in this proof. -/
theorem dynamic_bound (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) (choices : Choices) :
    ∃ result, Sequential.run choices (4 * (input.value.count.toNat + 2)) initial = .ok result ∧
      BufferCall.Post spec input initial result.state ∧
      result.instructions ≤ 4 * (input.value.count.toNat + 2) := by
  have binding : CFG.At bytes graph initial.rip valid.entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [valid.entry_offset]
  have count : initial.registers .rcx = input.value.count :=
    pre.arguments 3 (.word64 input.value.count) rfl
  have total := (annotations input initial pre).sound valid valid.entry_cutpoint
    binding (entry_invariant input initial pre) choices
  simpa [annotations, rank, CFG.Valid.entry, graph, count, Nat.add_assoc] using total

/-- At zero count even an arbitrary unmapped/noncanonical RDI is untouched.
The only reported reads have original caller-slot authority; no DATA read can
hide in an interior prefix or be admitted by readable memory outside a buffer. -/
theorem zero_no_data (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) (zero : input.value.count = 0#64)
    (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      BufferCall.Post spec input initial result.state ∧
      ∀ read ∈ result.reads, PureCall.RawRead initial read := by
  obtain ⟨executions, policy⟩ :=
    VCGen.bufferCall_raw_of_cutpoints spec bytes graph valid generated input initial pre
  obtain ⟨result, execution, post⟩ := executions choices
  refine ⟨result, execution, post, ?_⟩
  intro read member
  obtain ⟨_, _, _, _, _, _, _, _, _, allowed, _⟩ :=
    Grading.ReadOnlyPolicy.read_origin policy execution member
  simpa [BufferCall.RawRead, BufferCall.DataRead, spec, zero] using allowed

/-- A seven-byte snapshot cannot authorize an eight-byte operand, even if
all machine memory happens to be readable. This catches a missing width/end
check in the generated read VC independently of returned values. -/
def shortSpec : BufferCall.Spec :=
  { spec with buffers := fun input => [⟨input.base, (encoded input.value).take 7⟩] }

abbrev overreadGraph : CFG.Graph := ⟨[
  ⟨0, .loadMem64 .rax (.base .rdi), true, 1⟩,
  ⟨3, .legacy .ret, false, 0⟩], 1⟩

abbrev overreadEntry : overreadGraph.Index := ⟨0, by decide⟩

theorem overread_rejected (input : BufferCall.Invocation shortSpec) (initial : State)
    (base : initial.registers .rdi = input.value.base) :
    ¬VCGen.Cutpoints.wp overreadGraph initial.rip (fun _ => True)
      (fun _ read => BufferCall.RawRead shortSpec input initial read)
      (fun _ _ => True) (fun _ _ => 0) 0 2 overreadEntry initial := by
  intro generated
  have one := generated false
  simp only [CFG.Graph.node, overreadGraph, List.getElem_cons_zero] at one
  cases loaded : loadQWord initial.memory (initial.registers .rdi) with
  | error fault =>
    simp [execute, Address.eval, loaded] at one
  | ok value =>
    simp only [execute, Address.eval, loaded, ok_bind, pure_ok] at one
    have allowed := one.1 ⟨.data, initial.registers .rdi, 8⟩
      (by simp [Instruction.operandReads, Address.eval])
    rcases allowed with stack | ⟨_, buffer, member, positive, lower, upper⟩
    · cases stack.1
    · have same : buffer = ⟨input.value.base, (encoded input.value.value).take 7⟩ := by
        simpa [shortSpec, spec] using member
      subst buffer
      simp [base, encoded] at upper

end EDSL.Tests.BufferCallVCGen

elab "#audit_buffer_call_vcg" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``EDSL.X86.VCGen.Cutpoints.Annotations.block_memory,
    ``EDSL.X86.VCGen.Cutpoints.Annotations.readOnly_policy_memory,
    ``EDSL.X86.VCGen.Cutpoints.Annotations.total_policy,
    ``EDSL.X86.VCGen.bufferCall_raw_of_cutpoints,
    ``EDSL.X86.VCGen.bufferCall_semantics_of_cutpoints,
    ``EDSL.Tests.BufferCallVCGen.valid,
    ``EDSL.Tests.BufferCallVCGen.annotations,
    ``EDSL.Tests.BufferCallVCGen.semantics,
    ``EDSL.Tests.BufferCallVCGen.dynamic_bound,
    ``EDSL.Tests.BufferCallVCGen.zero_no_data,
    ``EDSL.Tests.BufferCallVCGen.overread_rejected]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless allowed.contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"
    Lean.logInfo m!"Allowed named audit passed: {name}"

#print axioms EDSL.X86.VCGen.bufferCall_semantics_of_cutpoints
#print axioms EDSL.Tests.BufferCallVCGen.semantics
#print axioms EDSL.Tests.BufferCallVCGen.dynamic_bound
#print axioms EDSL.Tests.BufferCallVCGen.zero_no_data
#print axioms EDSL.Tests.BufferCallVCGen.overread_rejected
#audit_buffer_call_vcg
