/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFG

namespace EDSL.X86.Sequential.CFG

variable {profile : Profile}

/-- Relative graph edges translated by the actual runtime code base. -/
def Targets (pc : Word) (instruction : Instruction) : List Word :=
  let fallthrough := pc + BitVec.ofNat 64 instruction.length
  let branch (displacement : Byte) := pc + 2 + displacement.signExtend 64
  match instruction with
  | .legacy .ret => []
  | .legacy (.jrcxz displacement) | .legacy (.loopRcx displacement)
  | .legacy (.jnz displacement) | .je displacement | .jcc _ displacement => [fallthrough, branch displacement]
  | .jmp displacement => [branch displacement]
  | _ => [fallthrough]

private theorem shortBranch_target {initial final : State} {taken : Bool} {displacement : Byte}
    (success : executeShortBranch initial taken displacement = .ok final) :
    final.rip = initial.rip + 2 ∨ final.rip = initial.rip + 2 + displacement.signExtend 64 := by
  unfold executeShortBranch at success
  split at success
  · dsimp only at success
    split at success
    · cases success; exact Or.inr rfl
    · cases success
  · cases success; exact Or.inl rfl

private theorem jump_target {initial final : State} {displacement : Byte}
    (success : executeShortBranch initial true displacement = .ok final) :
    final.rip = initial.rip + 2 + displacement.signExtend 64 := by
  simp only [executeShortBranch, ↓reduceIte] at success
  split at success
  · cases success; rfl
  · cases success

/-- Actual successful continuations follow one of the static ISA successors.
This theorem inverts the real executor; it does not execute through the graph. -/
theorem execute_next_target {initial final : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (allowed : readOnly instruction = true)
    (success : execute initial instruction af = .ok observation)
    (next : observation.result = .next final) :
    final.rip ∈ Targets initial.rip instruction := by
  cases instruction with
  | movzxMem8 destination address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_movzxMem8_success_iff.mp success
    cases next
    simp [Targets]
  | cmpMemImm8 address immediate =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemImm8_success_iff.mp success
    cases next
    simp [Targets]
  | cmpRegMem8 left address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_cmpRegMem8_success_iff.mp success
    cases next
    simp [Targets]
  | cmpMemReg8 address source =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemReg8_success_iff.mp success
    cases next
    simp [Targets]
  | cmpMemReg32 address source =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemReg32_success_iff.mp success
    cases next
    simp [Targets]
  | legacy old =>
    cases old with
    | storeEsiRdi | storeEaxRsi | exchangeEaxRdi | fetchAddEaxRdi | syscall =>
      simp [readOnly] at allowed
    | leaEaxRdiDisp8 displacement | leaEaxRaxDisp8 displacement
    | movEaxEdi | movEaxEsi | cmpEaxZero | mov32 destination value =>
      cases success
      cases next
      simp [Targets, Instruction.length, executeLea, executeLeaRax,
        executeMovEaxEdi, executeMovEaxEsi, executeCmpEaxZero, executeMov32]
    | loadEaxRdi =>
      cases loaded : loadDWord initial.memory (initial.registers .rdi) <;>
        simp [execute, X86.executeInstruction, executeLoad, loaded] at success
      cases success; cases next
      simp [Targets, Instruction.length]
    | loadEaxRsi =>
      cases loaded : loadDWord initial.memory (initial.registers .rsi) <;>
        simp [execute, X86.executeInstruction, executeLoadRsi, loaded] at success
      cases success; cases next
      simp [Targets, Instruction.length]
    | ret =>
      cases loaded : readWord initial.memory (initial.registers .rsp) <;>
        simp [execute, X86.executeInstruction, executeRet, loaded] at success
      split at success
      · cases success; cases next
      · cases success
    | jrcxz displacement =>
      cases branched : executeJrcxz initial displacement <;>
        simp [execute, X86.executeInstruction, branched] at success
      cases success; cases next
      simpa [Targets, Instruction.length] using shortBranch_target branched
    | loopRcx displacement =>
      cases branched : executeLoop initial displacement <;>
        simp [execute, X86.executeInstruction, branched] at success
      cases success; cases next
      simpa [Targets, Instruction.length, State.writeRegister] using
        shortBranch_target branched
    | jnz displacement =>
      cases branched : executeJnz initial displacement <;>
        simp [execute, X86.executeInstruction, branched] at success
      cases success; cases next
      simpa [Targets, Instruction.length] using shortBranch_target branched
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | negReg32 destination prefixed | bswapReg64 destination | shrOne64 destination | rolCL64 destination
  | movzxReg8 destination source prefixed | cmpReg8 left right prefixed
  | subReg32 destination source prefixed
  | xorSelf32 destination | movReg32 destination source | movReg64 destination source
  | setcc condition destination prefixed | movImm8 destination immediate prefixed | movSignImm32 destination immediate
  | cmovReg32 condition destination source prefixed | cmovReg64 condition destination source
  | lea64 destination address | addReg64 destination source | logicalReg64 operation destination source | xchgReg64 left right | xchgRax64 other
  | test32 left right prefixed | cmp32 left right prefixed | endbr64IbtDisabled | nop encoding
  | test64 left right | cmp64 left right
  | addImm32 destination immediate prefixed | inc32 destination prefixed
  | addImm64 destination immediate | inc64 destination | dec64 destination =>
    cases success; cases next
    simp [Targets, Instruction.length]
  | addMem32 destination address | loadMem32 destination address =>
    cases loaded : loadDWord initial.memory (address.eval initial) <;>
      simp [execute, loaded] at success
    cases success; cases next
    simp [Targets]
  | loadMem64 destination address | addMem64 destination address =>
    cases loaded : loadQWord initial.memory (address.eval initial) <;>
      simp [execute, loaded] at success
    cases success; cases next
    simp [Targets]
  | storeMem32 _ _ | storeMem64 _ _ => simp [readOnly] at allowed
  | je displacement =>
    cases branched : executeShortBranch initial (initial.flags.getLsbD 6) displacement <;>
      simp only [execute, branched, ok_bind, error_bind, pure_ok, Except.ok.injEq,
        reduceCtorEq] at success
    cases success; cases next
    simpa [Targets, Instruction.length] using shortBranch_target branched
  | jcc condition displacement =>
    cases branched : executeShortBranch initial (condition.holds initial.flags) displacement <;>
      simp only [execute, branched, ok_bind, error_bind, pure_ok, Except.ok.injEq,
        reduceCtorEq] at success
    cases success; cases next
    simpa [Targets, Instruction.length] using shortBranch_target branched
  | jmp displacement =>
    cases branched : executeShortBranch initial true displacement <;>
      simp [execute, branched] at success
    cases success; cases next
    simpa [Targets] using jump_target branched

/-- Read-only successful ordinary continuations preserve the full current RAM,
including accessibility/executability maps. -/
theorem execute_next_memory {initial final : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (allowed : readOnly instruction = true)
    (success : execute initial instruction af = .ok observation)
    (next : observation.result = .next final) : final.memory = initial.memory := by
  cases instruction with
  | legacy old =>
    have noStore : old.storeIntent initial = none := by
      cases old <;> simp_all [readOnly, X86.Instruction.storeIntent]
    cases result : X86.executeInstruction initial old <;> simp [execute, result] at success
    cases success
    cases next
    exact executeInstruction_ordinary_memory noStore (Or.inl result)
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | addImm32 _ _ _ | inc32 _ _
  | negReg32 _ _ | bswapReg64 _ | shrOne64 _ | rolCL64 _
  | movzxMem8 _ _ _ | movzxReg8 _ _ _ | cmpReg8 _ _ _ | subReg32 _ _ _
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | setcc _ _ _ | movImm8 _ _ _ | movSignImm32 _ _ | cmovReg32 _ _ _ _ | cmovReg64 _ _ _ | lea64 _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _ | loadMem32 _ _ | loadMem64 _ _ | test32 _ _ _ | cmp32 _ _ _ | cmpMemImm8 _ _ | cmpRegMem8 _ _ _ | cmpMemReg8 _ _ | cmpMemReg32 _ _ | endbr64IbtDisabled | nop _ | test64 _ _ | cmp64 _ _ | addMem32 _ _ | addMem64 _ _ | addImm64 _ _
  | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ =>
    exact execute_new_memory rfl rfl rfl success next
  | storeMem32 _ _ | storeMem64 _ _ => simp [readOnly] at allowed

/-- Every admitted successful instruction is an ordinary continuation or RET.
In particular neither a syscall nor a locked event can hide inside this profile. -/
theorem execute_result {initial : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (allowed : readOnly instruction = true)
    (success : execute initial instruction af = .ok observation) :
    ∃ final, observation.result = .next final ∨
      (observation.result = .returned final ∧ instruction = .legacy .ret) := by
  cases instruction with
  | legacy old =>
    cases old with
    | storeEsiRdi | storeEaxRsi | exchangeEaxRdi | fetchAddEaxRdi | syscall =>
      simp [readOnly] at allowed
    | leaEaxRdiDisp8 _ | leaEaxRaxDisp8 _ | movEaxEdi | movEaxEsi
    | cmpEaxZero | mov32 _ _ =>
      cases success
      exact ⟨_, Or.inl rfl⟩
    | loadEaxRdi =>
      cases loaded : loadDWord initial.memory (initial.registers .rdi) <;>
        simp [execute, X86.executeInstruction, executeLoad, loaded] at success
      cases success
      exact ⟨_, Or.inl rfl⟩
    | loadEaxRsi =>
      cases loaded : loadDWord initial.memory (initial.registers .rsi) <;>
        simp [execute, X86.executeInstruction, executeLoadRsi, loaded] at success
      cases success
      exact ⟨_, Or.inl rfl⟩
    | ret =>
      cases loaded : readWord initial.memory (initial.registers .rsp) <;>
        simp [execute, X86.executeInstruction, executeRet, loaded] at success
      split at success
      · cases success; exact ⟨_, Or.inr ⟨rfl, rfl⟩⟩
      · cases success
    | jrcxz displacement =>
      cases branched : executeJrcxz initial displacement <;>
        simp [execute, X86.executeInstruction, branched] at success
      cases success
      exact ⟨_, Or.inl rfl⟩
    | loopRcx displacement =>
      cases branched : executeLoop initial displacement <;>
        simp [execute, X86.executeInstruction, branched] at success
      cases success
      exact ⟨_, Or.inl rfl⟩
    | jnz displacement =>
      cases branched : executeJnz initial displacement <;>
        simp [execute, X86.executeInstruction, branched] at success
      cases success
      exact ⟨_, Or.inl rfl⟩
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | addImm32 _ _ _ | inc32 _ _
  | negReg32 _ _ | bswapReg64 _ | shrOne64 _ | rolCL64 _
  | movzxMem8 _ _ _ | movzxReg8 _ _ _ | cmpReg8 _ _ _ | subReg32 _ _ _
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | setcc _ _ _ | movImm8 _ _ _ | movSignImm32 _ _ | cmovReg32 _ _ _ _ | cmovReg64 _ _ _ | lea64 _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _ | loadMem32 _ _ | loadMem64 _ _ | test32 _ _ _ | cmp32 _ _ _ | cmpMemImm8 _ _ | cmpRegMem8 _ _ _ | cmpMemReg8 _ _ | cmpMemReg32 _ _ | endbr64IbtDisabled | nop _ | test64 _ _ | cmp64 _ _ | addMem32 _ _ | addMem64 _ _ | addImm64 _ _
  | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ =>
    obtain ⟨final, next⟩ := execute_new_next rfl success
    exact ⟨final, Or.inl next⟩
  | storeMem32 _ _ | storeMem64 _ _ => simp [readOnly] at allowed

theorem execute_returned_memory {initial final : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (allowed : readOnly instruction = true)
    (success : execute initial instruction af = .ok observation)
    (returned : observation.result = .returned final) : final.memory = initial.memory := by
  obtain ⟨output, next | ⟨ret, instructionEq⟩⟩ := execute_result allowed success
  · rw [returned] at next
    cases next
  · have same : output = final := StepResult.returned.inj (ret.symm.trans returned)
    subst output
    subst instruction
    cases result : X86.executeInstruction initial .ret <;> simp [execute, result] at success
    cases success
    cases returned
    exact executeInstruction_ordinary_memory rfl (Or.inr result)

theorem execute_returned_iff {initial : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (allowed : readOnly instruction = true)
    (success : execute initial instruction af = .ok observation) :
    (∃ final, observation.result = .returned final) ↔ instruction = .legacy .ret := by
  constructor
  · rintro ⟨final, returned⟩
    obtain ⟨_, next | ⟨_, instructionEq⟩⟩ := execute_result allowed success
    · rw [returned] at next
      cases next
    · exact instructionEq
  · intro instructionEq
    obtain ⟨final, next | ⟨returned, _⟩⟩ := execute_result allowed success
    · have target := execute_next_target allowed success next
      simp [instructionEq, Targets] at target
    · exact ⟨final, returned⟩

theorem targets_translate (node : Node) (base : Word) :
    Targets (base + BitVec.ofNat 64 node.offset) node.instruction =
      node.successors.map (fun target => base + target) := by
  cases instruction : node.instruction with
  | legacy old => cases old <;>
      simp [Targets, Node.successors, instruction, BitVec.ofNat_add, BitVec.add_assoc]
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | addImm32 _ _ _ | inc32 _ _
  | negReg32 _ _ | bswapReg64 _ | shrOne64 _ | rolCL64 _
  | movzxMem8 _ _ _ | movzxReg8 _ _ _ | cmpReg8 _ _ _ | subReg32 _ _ _
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | setcc _ _ _ | movImm8 _ _ _ | movSignImm32 _ _ | cmovReg32 _ _ _ _ | cmovReg64 _ _ _ | lea64 _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _ | loadMem32 _ _ | storeMem32 _ _ | loadMem64 _ _ | storeMem64 _ _
  | test32 _ _ _ | cmp32 _ _ _ | cmpMemImm8 _ _ | cmpRegMem8 _ _ _ | cmpMemReg8 _ _ | cmpMemReg32 _ _ | endbr64IbtDisabled | nop _ | test64 _ _ | cmp64 _ _ | addMem32 _ _ | addMem64 _ _ | addImm64 _ _
  | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ =>
      simp [Targets, Node.successors, instruction, BitVec.ofNat_add, BitVec.add_assoc]

/-- A real successful continuation identifies a checked destination. Its code
binding is retained because admitted instructions preserve actual current RAM. -/
theorem Valid.next {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {base : Word} {initial final : State} (code : CodeAt initial.memory base bytes)
    (index : graph.Index)
    (currentPC : initial.rip = base + BitVec.ofNat 64 (graph.node index).offset)
    {af : Bool} {observation : Observation} (success : step af initial = .ok observation)
    (next : observation.result = .next final) :
    ∃ destination : graph.Index, graph.Edge index destination ∧
      final.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
      final.memory = initial.memory ∧ CodeAt final.memory base bytes := by
  have executed : execute initial (graph.node index).instruction af = .ok observation := by
    rwa [valid.step_eq_execute code index initial rfl currentPC af] at success
  have allowed := (valid.nodes index).2.2.1
  have target := execute_next_target allowed executed next
  rw [currentPC, targets_translate] at target
  obtain ⟨offset, member, actual⟩ := List.mem_map.mp target
  obtain ⟨destination, same⟩ := valid.closed index offset member
  have memory := execute_next_memory allowed executed next
  refine ⟨destination, ?_, ?_, memory, ?_⟩
  · change BitVec.ofNat 64 (graph.node destination).offset ∈ (graph.node index).successors
    rw [same]
    exact member
  · exact actual.symm.trans (congrArg (fun value => base + value) same.symm)
  · rw [memory]
    exact code

theorem Valid.returned {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {base : Word} {initial final : State} (code : CodeAt initial.memory base bytes)
    (index : graph.Index)
    (currentPC : initial.rip = base + BitVec.ofNat 64 (graph.node index).offset)
    {af : Bool} {observation : Observation} (success : step af initial = .ok observation)
    (returned : observation.result = .returned final) :
    (graph.node index).instruction = .legacy .ret ∧
      final.memory = initial.memory ∧ CodeAt final.memory base bytes := by
  have executed : execute initial (graph.node index).instruction af = .ok observation := by
    rwa [valid.step_eq_execute code index initial rfl currentPC af] at success
  have allowed := (valid.nodes index).2.2.1
  have memory := execute_returned_memory allowed executed returned
  refine ⟨?_, memory, ?_⟩
  · obtain ⟨output, next | ⟨_, instructionEq⟩⟩ := execute_result allowed executed
    · rw [returned] at next
      cases next
    · exact instructionEq
  · rw [memory]
    exact code

theorem Valid.result {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {base : Word} {initial : State} (code : CodeAt initial.memory base bytes)
    (index : graph.Index)
    (currentPC : initial.rip = base + BitVec.ofNat 64 (graph.node index).offset)
    {af : Bool} {observation : Observation} (success : step af initial = .ok observation) :
    ∃ final, observation.result = .next final ∨
      (observation.result = .returned final ∧ (graph.node index).instruction = .legacy .ret) := by
  have executed : execute initial (graph.node index).instruction af = .ok observation := by
    rwa [valid.step_eq_execute code index initial rfl currentPC af] at success
  exact execute_result (valid.nodes index).2.2.1 executed

theorem Valid.no_atomic {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {base : Word} {initial : State} (code : CodeAt initial.memory base bytes)
    (index : graph.Index)
    (currentPC : initial.rip = base + BitVec.ofNat 64 (graph.node index).offset)
    {af : Bool} {observation : Observation} (success : step af initial = .ok observation)
    (event : AtomicEvent) (final : State) : observation.result ≠ .atomic event final := by
  intro atomic
  obtain ⟨_, next | ⟨returned, _⟩⟩ := valid.result code index currentPC success
  · rw [atomic] at next
    cases next
  · rw [atomic] at returned
    cases returned

theorem Valid.no_syscall {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {base : Word} {initial : State} (code : CodeAt initial.memory base bytes)
    (index : graph.Index)
    (currentPC : initial.rip = base + BitVec.ofNat 64 (graph.node index).offset)
    {af : Bool} {observation : Observation} (success : step af initial = .ok observation)
    (request : SyscallRequest) : observation.result ≠ .syscall request := by
  intro syscall
  obtain ⟨_, next | ⟨returned, _⟩⟩ := valid.result code index currentPC success
  · rw [syscall] at next
    cases next
  · rw [syscall] at returned
    cases returned

end EDSL.X86.Sequential.CFG
