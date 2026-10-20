/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Coverage
import tests.fixtures.CallStack.CPUFixture
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallStackCoverage
open X86 OS OS.StackFrame CallStack
open EDSL.Tests.StackFrameCPU

-- Reuse the initialized, owned synthetic CALL/helper-RET/caller-RET machine
-- trace. Each receipt binds the actual decode to the full seven-byte extent.
theorem covered_trace (choices : CallReturn.Choices) :
    CoveredExecution frame choices seed start calledWorld
      ⟨finished, 3, [⟨.stack,65536,8⟩,⟨.stack,65544,8⟩]⟩ := by
  exact .next (callStep (choices 0)) ⟨0, .callRelative32 1, rfl, rfl, by decide⟩
    (.next (internalStep ((choices.drop 1) 0))
      ⟨6, .sequential (.legacy .ret), rfl, rfl, by decide⟩
      (.ret (terminalStep (((choices.drop 1).drop 1) 0))
        ⟨5, .sequential (.legacy .ret), rfl, rfl, by decide⟩))

-- The real whole-code binding and current resources accompany successful
-- evaluation. The actual terminal target is not even decodable; coverage must
-- not impose a fetch condition there or stop at the first internal RET.
theorem covered_run (choices : CallReturn.Choices) :
    CodeAt start.memory frame.call.code frame.call.bytes ∧
      CallReturn.runFrom frame.top choices 3 start =
        .ok ⟨finished, 3, [⟨.stack,65536,8⟩,⟨.stack,65544,8⟩]⟩ ∧
      Current frame calledWorld finished ∧ Preservation frame seed calledWorld ∧
      ¬FetchWithin frame finished := by
  have trace := covered_trace choices
  refine ⟨?_, CallReturn.runFrom_complete trace.machine (by decide),
    trace.current startCurrent, trace.preserves, ?_⟩
  · rw [startCurrent.coupled]
    exact startCurrent.contract.pureCall.code
  · intro fetched
    obtain ⟨_, _, _, observed, _⟩ := fetched
    have fault : CallReturn.decodeAt finished = .error (.inaccessibleInstruction finished.rip) := rfl
    rw [fault] at observed
    cases observed

def shortImmediate : Descriptor :=
  { frame with call := { frame.call with bytes := frame.call.bytes.take 4 } }

-- Actual RAM still decodes the entire CALL, but its last immediate byte lies
-- outside this selected extent. An opcode-only or start-only bound is unsound.
theorem reject_truncated_immediate (choices : CallReturn.Choices) :
    ¬∃ evolved result, CoveredExecution shortImmediate choices seed start evolved result := by
  intro ⟨_, _, trace⟩
  have bound : 5 ≤ 4 := trace.fetchWithin.length_le
    (show CallReturn.decodeAt start = .ok (.callRelative32 1) from rfl)
  omega

def shortHelper : Descriptor :=
  { frame with call := { frame.call with bytes := frame.call.bytes.take 6 } }

-- The complete CALL fits this extent. Its actual helper RET is at offset six,
-- so the first real prefix reaches an uncovered instruction. Determinism
-- prevents any covered returning trace from substituting another path/result.
theorem reject_truncated_helper (choices : CallReturn.Choices) :
    ¬∃ evolved result, CoveredExecution shortHelper choices seed start evolved result := by
  intro ⟨_, result, trace⟩
  have actual : CallReturn.ExecutesFrom frame.top choices start result := trace.machine
  have same := actual.fixed_choices_unique (complete choices).machine
  have cost : result.instructions = 3 := congrArg Sequential.Result.instructions same
  have block : CallReturn.BlockFrom shortHelper.top choices start called 1 [] :=
    .next (callStep (choices 0)).machine .nil
  have fetched := trace.prefix block (by rw [cost]; decide)
  have bound : 6 + 1 ≤ 6 :=
    (FetchWithin.atOffset_iff (frame := shortHelper) (instruction := .sequential (.legacy .ret))
      (offset := 6) (by decide) (by decide) rfl rfl).mp fetched
  omega

def shortTerminal : Descriptor :=
  { frame with call := { frame.call with bytes := frame.call.bytes.take 5 } }

-- Starting at the real terminal RET pre-state also requires its own encoding
-- to fit. Successful raw return from that state grants no fetch exemption.
theorem reject_truncated_terminal (choices : CallReturn.Choices) :
    ¬∃ evolved result, CoveredExecution shortTerminal choices calledWorld resumed evolved result := by
  intro ⟨_, _, trace⟩
  have bound : 5 + 1 ≤ 5 :=
    (FetchWithin.atOffset_iff (frame := shortTerminal) (instruction := .sequential (.legacy .ret))
      (offset := 5) (by decide) (by decide) rfl rfl).mp trace.fetchWithin
  omega

end EDSL.Tests.CallStackCoverage

#print axioms EDSL.Tests.CallStackCoverage.covered_trace
#print axioms EDSL.Tests.CallStackCoverage.covered_run
#print axioms EDSL.Tests.CallStackCoverage.reject_truncated_immediate
#print axioms EDSL.Tests.CallStackCoverage.reject_truncated_helper
#print axioms EDSL.Tests.CallStackCoverage.reject_truncated_terminal
#audit_edsl
