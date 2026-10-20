/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.Cutpoints
import tests.fixtures.CallMemory64.Inline
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64Cutpoints
open X86 OS OS.CallMemory64
open EDSL.CallMemory64 (Resources ResourcePre Post resourceInput)
open EDSL.CallMemory64.Inline

inductive Node where
  | store | increment | ret

/-- The first segment retires two instructions, so its successor must use
`choices.drop 2`, not a reset stream or a drop by the number of segments. -/
def flow : Sequential.Cutpoints.Layout Node where
  cutpoint := fun node => match node with | .store | .ret => true | .increment => false
  depth := fun node => match node with | .store => 1 | .increment | .ret => 0
  maxDepth := 1
  Edge := fun node dest => match node, dest with
    | .store, .increment | .increment, .ret => True
    | _, _ => False
  depth_bound := by intro node; cases node <;> decide
  depth_decrease := by
    intro node dest edge ordinary
    cases node <;> cases dest <;> simp_all

def Readback (resource : Resources) (shared : Shared) : Prop :=
  Borrowing.loadOwnedWord64 shared resource.descriptor.owner resource.descriptor.ticket
    resource.descriptor.target = .ok resource.value

/-- Annotations retain a past store's current owner readback and preservation.
They contain no future run, future history or assertion of the final contract. -/
def Ready (resource : Resources) (initial : State) (node : Node)
    (shared : Shared) (state : State) : Prop :=
  match node with
  | .store => shared = resource.shared ∧ state = initial
  | .increment => state = stored initial shared ∧ Readback resource shared ∧
      Preservation resource.descriptor resource.shared shared
  | .ret => state = increment (stored initial shared) ∧ Readback resource shared ∧
      Preservation resource.descriptor resource.shared shared

def Inside (resource : Resources) (initial : State) (source : Node) (budget : Nat)
    (node : Node) (shared : Shared) (state : State) : Prop :=
  match node with
  | .store | .increment => source = .store ∧ budget = 1 ∧ Ready resource initial node shared state
  | .ret => Ready resource initial node shared state

/-- Independent arithmetic, DATA, return, ABI and union-frame contract. Its
proof uses present coupled RAM and past preservation, with no assumed return. -/
theorem terminal_post {resource initial shared}
    (pre : ResourcePre program resource initial)
    (current : Current resource.descriptor shared (finish resource initial shared))
    (readback : Readback resource shared)
    (preservation : Preservation resource.descriptor resource.shared shared) :
    Post (resourceInput resource) initial (finish resource initial shared) := by
  have frame := OS.CallMemory64.memory_frame pre.current current preservation
  refine ⟨?_, ?_, frame.1, frame.2.1, frame.2.2, rfl, ?_, preserved, rfl⟩
  · change (initial.registers .rsi + 1).toNat = EDSL.CallMemory64.resultNat resource.value
    rw [pre.argument]
    exact EDSL.CallMemory64.one_addition resource.value
  · rw [current.coupled]
    exact Borrowing.loadOwnedWord64_readWord _ _ _ _ _ readback
  · rfl

/-- A real decoded store/LEA/RET certificate with a two-instruction segment
and a decreasing-rank edge to the original-slot RET. The independent `Post`
is closed over the arbitrary initial caller context. -/
def certificate {resource initial} (pre : ResourcePre program resource initial) :
    Cutpoints.Certificate flow resource.descriptor
      (fun _ final => Post (resourceInput resource) initial final) where
  Inv := Ready resource initial
  rank := fun node _ _ => match node with | .store => 1 | .increment | .ret => 0
  Interior := Inside resource initial
  start := by
    intro cut shared state isCut valid
    cases cut with
    | store => exact ⟨rfl, rfl, valid⟩
    | increment => cases isCut
    | ret => exact valid
  localVC := by
    intro source budget node shared before interior current af
    cases node with
    | store =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := interior
      obtain ⟨evolved, step, _, readback⟩ := store_enabled pre af
      refine ⟨evolved, _, _, step, store_fetch pre, Node.increment, trivial, .inr ?_⟩
      exact ⟨rfl, rfl, rfl, rfl, readback, step.history.preserves⟩
    | increment =>
      obtain ⟨rfl, rfl, rfl, readback, preservation⟩ := interior
      have step := increment_step current pre.code (stored_pc pre shared) af
      refine ⟨shared, _, _, step, increment_fetch current pre.code (stored_pc pre shared),
        Node.ret, trivial, .inl ?_⟩
      exact ⟨rfl, ⟨rfl, readback, preservation⟩, by decide⟩
    | ret =>
      obtain ⟨rfl, readback, preservation⟩ := interior
      have decoded := decode_ret current pre.code (increment_pc pre shared)
      have step := CPU.lift_stack (descriptor := resource.descriptor)
        (StackFrame.CPU.original_ret_step current.stack (increment_stack pre shared) af decoded)
      exact ⟨shared, _, _, step, ret_fetch current pre.code (increment_pc pre shared),
        terminal_post pre (step.current current) readback preservation⟩

/-- The generic certificate proves the existing externally defined semantic
claim, including full64 wraparound, arbitrary old DATA, ABI and RAM framing. -/
theorem semantic_claim : EDSL.CallMemory64.SemanticClaim program := by
  intro resource initial pre choices
  obtain ⟨evolved, result, trace, post, _⟩ :=
    (certificate pre).execution (entry := .store) rfl ⟨rfl, rfl⟩ pre.current choices
  exact ⟨evolved, result, trace, post⟩

/-- Actual reachable domain, arbitrary scalar input/old word/GPRs/flags, all
AF streams. This checks an independent return/data/ABI contract rather than
the annotations' assigned states. The bound 4 comes from static depth 1 and
dynamic rank 1; evaluator success and resource endpoints are derived. -/
theorem concrete_contract (input old : Word) (registers : Register → Word) (flags : Word)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices 4
        (EDSL.CallMemory64.Domain.initial program input old registers flags) = .ok result ∧
      EDSL.CallMemory64.Returned (EDSL.CallMemory64.Domain.resource program input old)
        (EDSL.CallMemory64.Domain.initial program input old registers flags) choices evolved result ∧
      result.instructions ≤ 4 := by
  have pre := EDSL.CallMemory64.Domain.resource_pre program (by decide) (by decide)
    input old registers flags
  obtain ⟨evolved, result, ran, trace, post, bound⟩ :=
    (certificate pre).total (entry := .store) rfl ⟨rfl, rfl⟩ pre.current choices
  exact ⟨evolved, result, ran, EDSL.CallMemory64.Returned.of_covered pre trace post, bound⟩

/-- The prefix-composition API also accepts independently supplied covered
prefixes, including their actual DATA mutation. It does not assume the prefix
was built by this certificate or require the initial CPU to be a cutpoint. -/
theorem resume_at_ret {resource initial choices shared before count reads}
    (pre : ResourcePre program resource initial)
    (history : CoveredHistory resource.descriptor choices resource.shared initial
      shared before count reads)
    (pc : before = increment (stored initial shared)) (readback : Readback resource shared) :
    ∃ evolved result,
      EDSL.CallMemory64.Returned resource initial choices evolved result ∧
      result.instructions ≤ count + 1 := by
  obtain ⟨evolved, result, trace, post, bound⟩ :=
    (certificate pre).after_history (entry := .ret) history rfl
      ⟨pc, readback, history.preserves⟩ pre.current
  exact ⟨evolved, result, EDSL.CallMemory64.Returned.of_covered pre trace post, bound⟩

end EDSL.Tests.CallMemory64Cutpoints

#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.segment
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.execution
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.instructionBound_le
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.total
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.actual
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.after_history
#print axioms EDSL.Tests.CallMemory64Cutpoints.terminal_post
#print axioms EDSL.Tests.CallMemory64Cutpoints.certificate
#print axioms EDSL.Tests.CallMemory64Cutpoints.semantic_claim
#print axioms EDSL.Tests.CallMemory64Cutpoints.concrete_contract
#print axioms EDSL.Tests.CallMemory64Cutpoints.resume_at_ret
#audit_edsl
