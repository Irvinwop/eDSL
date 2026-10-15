/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Machine
import EDSL.X86.StoreBuffer

/-! Memory-parametric facts for the supported x86 evaluator. These transport
current executions and their exact errors, using complete states and memories.
The underlying ordinary-RAM and locked-operand profile is unchanged. -/

namespace EDSL.X86

/-- Decode depends only on the instruction pointer and executable byte fetches,
including their exact errors. No data-memory equality is required. -/
theorem decodeAt_fetch_congr (a b : State) (pc : a.rip = b.rip)
    (fetch : ∀ address, fetchByte a.memory address = fetchByte b.memory address) :
    decodeAt a = decodeAt b := by
  unfold decodeAt
  simp only [fetch, pc]

/-- The supported instructions whose execution observes only private context.
Taken short branches retain the machine's canonical-target rejection. -/
def ContextOnly : Instruction → Prop
  | .leaEaxRdiDisp8 _ | .leaEaxRaxDisp8 _ | .movEaxEdi | .movEaxEsi
  | .mov32 _ _ | .cmpEaxZero | .jnz _ | .jrcxz _ | .loopRcx _ => True
  | _ => False

/-- Change memory throughout an architectural outcome, preserving every private
register, flag, instruction pointer, event and syscall continuation. -/
def StepResult.mapMemory (function : Memory → Memory) : StepResult → StepResult
  | .next output => .next { output with memory := function output.memory }
  | .atomic event output => .atomic event { output with memory := function output.memory }
  | .returned output => .returned { output with memory := function output.memory }
  | .syscall request => .syscall
      { request with user := { request.user with memory := function request.user.memory } }

private theorem executeShortBranch_memory_eq (input : State) (memory : Memory)
    (taken : Bool) (displacement : Byte) :
    executeShortBranch { input with memory := memory } taken displacement =
      (executeShortBranch input taken displacement).map
        (fun output => { output with memory := memory }) := by
  unfold executeShortBranch
  cases taken <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · rfl
  · split <;> rfl

/-- Exact execution transport, including rejection, for context-only operations.
The complete output context is retained even when data memories differ. -/
theorem execute_contextOnly_memory_eq (input : State) (memory : Memory)
    (instruction : Instruction) (contextOnly : ContextOnly instruction) :
    executeInstruction { input with memory := memory } instruction =
      (executeInstruction input instruction).map (StepResult.mapMemory (fun _ => memory)) := by
  cases instruction <;> simp only [ContextOnly] at contextOnly
  all_goals try contradiction
  all_goals try rfl
  case jrcxz displacement =>
    simp only [executeInstruction, executeJrcxz]
    rw [executeShortBranch_memory_eq input memory]
    cases executeShortBranch input (decide (input.registers .rcx = 0)) displacement <;> rfl
  case loopRcx displacement =>
    simp only [executeInstruction, executeLoop]
    have updated : ({ input with memory := memory }.writeRegister .rcx
        (input.registers .rcx - 1)) =
        { input.writeRegister .rcx (input.registers .rcx - 1) with memory := memory } := rfl
    rw [updated, executeShortBranch_memory_eq
      (input.writeRegister .rcx (input.registers .rcx - 1)) memory]
    cases executeShortBranch (input.writeRegister .rcx (input.registers .rcx - 1))
      (decide (input.registers .rcx - 1 ≠ 0)) displacement <;> rfl
  case jnz displacement =>
    simp only [executeInstruction, executeJnz]
    rw [executeShortBranch_memory_eq input memory]
    cases executeShortBranch input (!input.flags.getLsbD 6) displacement <;> rfl

/-- Successful context-only execution transports its whole output state. -/
theorem execute_contextOnly_memory (input output : State) (memory : Memory)
    (instruction : Instruction) (contextOnly : ContextOnly instruction)
    (ran : executeInstruction input instruction = .ok (.next output)) :
    executeInstruction { input with memory := memory } instruction =
      .ok (.next { output with memory := memory }) := by
  rw [execute_contextOnly_memory_eq input memory instruction contextOnly, ran]
  rfl

/-- Exact RSI load, including zero extension and all unchanged context fields. -/
theorem execute_load_exact (input : State) (value : BitVec 32)
    (read : loadDWord input.memory (input.registers .rsi) = .ok value) :
    executeInstruction input .loadEaxRsi = .ok (.next
      { input.writeRegister .rax (value.setWidth 64) with rip := input.rip + 2 }) := by
  simp [executeInstruction, executeLoadRsi, read]

/-- The same exact contract for the supported RDI load. -/
theorem execute_load_rdi_exact (input : State) (value : BitVec 32)
    (read : loadDWord input.memory (input.registers .rdi) = .ok value) :
    executeInstruction input .loadEaxRdi = .ok (.next
      { input.writeRegister .rax (value.setWidth 64) with rip := input.rip + 2 }) := by
  simp [executeInstruction, executeLoad, read]

/-- Exact ordinary store through RSI; it changes no register or flag. -/
theorem execute_store_exact (input : State)
    (allowed : canStoreDWord input.memory (input.registers .rsi) = true) :
    executeInstruction input .storeEaxRsi = .ok (.next { input with
      memory := writeDWordUnchecked input.memory (input.registers .rsi)
        ((input.registers .rax).setWidth 32), rip := input.rip + 2 }) := by
  rw [executeInstruction_storeEaxRsi, allowed]
  rfl

/-- Exact ordinary store through RDI, using the existing checked store theorem. -/
theorem execute_store_rdi_exact (input : State)
    (allowed : canStoreDWord input.memory (input.registers .rdi) = true) :
    executeInstruction input .storeEsiRdi = .ok (.next { input with
      memory := writeDWordUnchecked input.memory (input.registers .rdi)
        ((input.registers .rsi).setWidth 32), rip := input.rip + 2 }) := by
  rw [executeInstruction_storeEsiRdi, allowed]
  rfl

/-- RET changes exactly RSP and RIP. It neither changes memory nor drains any
buffer; the saved target's accessibility and canonicality are explicit. -/
theorem execute_ret_exact (input : State) (target : Word)
    (read : readWord input.memory (input.registers .rsp) = .ok target)
    (valid : canonical target = true) :
    executeInstruction input .ret = .ok (.returned
      { input.writeRegister .rsp (input.registers .rsp + 8) with rip := target }) := by
  simp [executeInstruction, executeRet, read, valid]

/-- Complete exchange execution from the actual checked memory operation. -/
theorem execute_exchange_exact (input : State) (memory : Memory) (old : BitVec 32)
    (ran : exchangeDWord input.memory (input.registers .rdi)
      ((input.registers .rax).setWidth 32) = .ok (memory, old)) :
    executeInstruction input .exchangeEaxRdi = .ok (.atomic
      ⟨input.registers .rdi, old, (input.registers .rax).setWidth 32⟩
      { input.writeRegister .rax (old.setWidth 64) with
        memory := memory
        rip := input.rip + 2 }) := by
  simp [executeInstruction, executeExchange, ran]

namespace StoreBuffer

/-- Symmetric modular footprint separation gives the read-frame premise. -/
theorem Separate.disjoint {left right : Word} (separate : Separate left right) :
    DWordDisjoint left right 4 := by
  intro offset bound
  have inside : ((right + BitVec.ofNat 64 offset) - right).toNat < 4 := by
    rw [BitVec.add_comm right _, BitVec.add_sub_cancel]
    simpa only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega)] using bound
  exact (separate _).resolve_right (by omega)

end StoreBuffer

/-- An exchange passes independent pending writes as an equality of complete
Memory structures. Forward transport needs no checkedness premise. -/
theorem ExchangeTransition.view {m m' : Memory} {e : AtomicEvent}
    (transition : ExchangeTransition m e m') (buffer : StoreBuffer.Buffer)
    (separate : ∀ store ∈ buffer, StoreBuffer.Separate store.address e.address) :
    ExchangeTransition (StoreBuffer.view m buffer) e (StoreBuffer.view m' buffer) := by
  refine ⟨transition.1, StoreBuffer.view_canStore m buffer e.address transition.2.1, ?_, ?_⟩
  · rw [StoreBuffer.view_load_frame m buffer e.address
      (fun store member => (separate store member).disjoint)]
    exact transition.2.2.1
  · rw [transition.2.2.2]
    exact StoreBuffer.view_write_commute m buffer e.address e.after separate

/-- Exact, error-preserving exchange transport in both directions. Checked
pending stores preserve the accessible-byte domain, so the view cannot create
writability and conceal a physical write rejection. -/
theorem exchangeDWord_view (memory : Memory) (buffer : StoreBuffer.Buffer)
    (address : Word) (replacement : BitVec 32)
    (checked : ∀ store ∈ buffer, canStoreDWord memory store.address = true)
    (separate : ∀ store ∈ buffer, StoreBuffer.Separate store.address address) :
    exchangeDWord (StoreBuffer.view memory buffer) address replacement =
      (exchangeDWord memory address replacement).map
        (fun result => (StoreBuffer.view result.1 buffer, result.2)) := by
  unfold exchangeDWord
  rw [StoreBuffer.view_canStore_eq memory buffer address checked,
    StoreBuffer.view_load_frame memory buffer address
      (fun store member => (separate store member).disjoint)]
  by_cases supported : atomicAddressable address = true
  · by_cases allowed : canStoreDWord memory address = true
    · cases loadDWord memory address with
      | error fault => simp [supported, allowed, Except.map]
      | ok old =>
        simp [supported, allowed, Except.map,
          StoreBuffer.view_write_commute memory buffer address replacement separate]
    · simp [supported, allowed, Except.map]
  · simp [supported, Except.map]

/-- Exact exchange output event and full private context across a checked view. -/
theorem executeExchange_view (input : State) (buffer : StoreBuffer.Buffer)
    (checked : ∀ store ∈ buffer, canStoreDWord input.memory store.address = true)
    (separate : ∀ store ∈ buffer,
      StoreBuffer.Separate store.address (input.registers .rdi)) :
    executeExchange { input with memory := StoreBuffer.view input.memory buffer } =
      (executeExchange input).map (fun result =>
        (result.1, { result.2 with memory := StoreBuffer.view result.2.memory buffer })) := by
  unfold executeExchange
  dsimp only
  rw [exchangeDWord_view input.memory buffer _ _ checked separate]
  cases exchangeDWord input.memory (input.registers .rdi)
      ((input.registers .rax).setWidth 32) <;> rfl

/-- Instruction-level transport preserves errors, the actual atomic event and
every context field, and overlays the complete output memory. -/
theorem execute_exchange_view (input : State) (buffer : StoreBuffer.Buffer)
    (checked : ∀ store ∈ buffer, canStoreDWord input.memory store.address = true)
    (separate : ∀ store ∈ buffer,
      StoreBuffer.Separate store.address (input.registers .rdi)) :
    executeInstruction { input with memory := StoreBuffer.view input.memory buffer }
        .exchangeEaxRdi =
      (executeInstruction input .exchangeEaxRdi).map
        (StepResult.mapMemory (fun memory => StoreBuffer.view memory buffer)) := by
  simp only [executeInstruction]
  rw [executeExchange_view input buffer checked separate]
  cases executeExchange input <;> rfl

/-- Logical-view success constructs physical-global success with the same
complete context and event. No future physical success is an input. -/
theorem execute_exchange_view_iff (input : State) (buffer : StoreBuffer.Buffer)
    (checked : ∀ store ∈ buffer, canStoreDWord input.memory store.address = true)
    (separate : ∀ store ∈ buffer,
      StoreBuffer.Separate store.address (input.registers .rdi))
    (event : AtomicEvent) (logicalOutput : State) :
    executeInstruction { input with memory := StoreBuffer.view input.memory buffer }
        .exchangeEaxRdi = .ok (.atomic event logicalOutput) ↔
      ∃ output, executeInstruction input .exchangeEaxRdi = .ok (.atomic event output) ∧
        logicalOutput = { output with memory := StoreBuffer.view output.memory buffer } := by
  rw [execute_exchange_view input buffer checked separate]
  cases ran : executeInstruction input .exchangeEaxRdi with
  | error fault => simp [Except.map]
  | ok result =>
    cases result with
    | next output | returned output | syscall request =>
      simp [Except.map, StepResult.mapMemory]
    | atomic actual output =>
      simp only [Except.map, StepResult.mapMemory, Except.ok.injEq, StepResult.atomic.injEq]
      constructor
      · rintro ⟨events, same⟩
        exact ⟨output, ⟨events, rfl⟩, same.symm⟩
      · rintro ⟨physical, ⟨events, same⟩, view⟩
        subst physical
        exact ⟨events, view.symm⟩

end EDSL.X86
