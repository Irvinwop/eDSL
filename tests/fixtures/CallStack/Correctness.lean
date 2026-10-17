/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.GCCSame
import tests.fixtures.CallStack.Padded

set_option warningAsError true

namespace EDSL.CallStack.Compiler
open X86 OS

def instructionCount (profile : Profile) : Nat := if padded profile then 7 else 5

def reads (profile : Profile) (top : Word) : List CallReturn.Read :=
  if padded profile then [⟨.stack, top - 16, 8⟩, ⟨.stack, top - 8, 8⟩, ⟨.stack, top, 8⟩]
  else [⟨.stack, top - 8, 8⟩, ⟨.stack, top, 8⟩]

theorem gccSame_covered_checked {resource : Resources} {initial : State}
    (pre : ResourcePre (program .gccSame) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      CoveredExecution resource.frame choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = instructionCount .gccSame ∧ result.reads = reads .gccSame resource.frame.top := by
  obtain ⟨evolved, preceding, last, fetch, post⟩ := GCCSame.covered_correct pre choices
  have terminal : CoveredExecution resource.frame (choices.drop 4) evolved
      (GCCSame.afterIncrement initial) evolved
      ⟨GCCSame.final initial resource.frame.call.returnAddress, 1, [⟨.stack, resource.frame.top, 8⟩]⟩ := .ret last fetch
  have actual := preceding.then_execution terminal
  exact ⟨evolved, _, actual, post, rfl, rfl⟩

/-- All four complete compiler windows meet one independent contract, for all
64-bit inputs and all undefined-AF streams. Every store/read is tied to the
same threaded CPU/OS execution; both internal and original RET are included. -/
theorem covered_checked (profile : Profile) {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      CoveredExecution resource.frame choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = instructionCount profile ∧ result.reads = reads profile resource.frame.top := by
  cases profile with
  | gccSame => exact gccSame_covered_checked pre choices
  | gccSeparate =>
    obtain ⟨evolved, result, actual, cost, trace, post⟩ := Padded.gcc_covered pre choices
    exact ⟨evolved, result, actual, post, cost, trace⟩
  | clangSame =>
    obtain ⟨evolved, result, actual, cost, trace, post⟩ := Padded.clang_covered (Or.inl rfl) pre choices
    exact ⟨evolved, result, actual, post, cost, trace⟩
  | clangSeparate =>
    obtain ⟨evolved, result, actual, cost, trace, post⟩ := Padded.clang_covered (Or.inr rfl) pre choices
    exact ⟨evolved, result, actual, post, cost, trace⟩

/-- Each actual fetch, including internal and original RET, fits the exact
whole compiler text fixed by `ResourcePre`. The result also meets the
independent arithmetic, ABI, memory and resource contract. -/
theorem covered (profile : Profile) {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      CoveredExecution resource.frame choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨evolved, result, actual, post, _, _⟩ := covered_checked profile pre choices
  exact ⟨evolved, result, actual, post⟩

theorem checked (profile : Profile) {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = instructionCount profile ∧ result.reads = reads profile resource.frame.top := by
  obtain ⟨evolved, result, actual, post, cost, trace⟩ := covered_checked profile pre choices
  exact ⟨evolved, result, actual.execution, post, cost, trace⟩

/-- The concrete public evaluator terminates with the contract and reusable
current resources. Counts describe these exact programs, not hardware cycles
or a minimum over all implementations. -/
theorem evaluated (profile : Profile) {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      CallReturn.run choices (instructionCount profile) initial = .ok result ∧
      StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved result ∧
      StackFrame.Current resource.frame evolved result.state ∧
      StackFrame.Preservation resource.frame resource.shared evolved ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = instructionCount profile ∧ result.reads = reads profile resource.frame.top := by
  obtain ⟨evolved, result, actual, post, cost, trace⟩ := checked profile pre choices
  have machine : CallReturn.Executes choices initial result := by
    change CallReturn.ExecutesFrom (initial.registers .rsp) choices initial result
    rw [pre.stack]
    exact actual.machine
  exact ⟨evolved, result, CallReturn.run_complete machine (Nat.le_of_eq cost), actual,
    actual.current pre.current, actual.preserves, post, cost, trace⟩

end EDSL.CallStack.Compiler
