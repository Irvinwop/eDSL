/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumResources
import EDSL.Corpus.V1.SignumCertificatesFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.SignumResources
open X86 X86.Sequential OS
open Corpus.V1
open Corpus.V1.SignumResources

/-- Observe the signed low32 numeric result of the actual selected-address
installed caller. Complete loaded memory, the original caller return, RSP+8
and the same current code/caller resources remain part of the conclusion. -/
private def Returns (compiler : Compiler) (value : BitVec 32) (expected : Int)
    (choices : ChoiceStream FlagChoices) : Prop :=
  ∃ result, ExecutesWith choices (loadedCall compiler value).initial result ∧
    (loadedCall compiler value).initial.rip = (input compiler).function.window.base ∧
    ((result.state.registers .rax).setWidth 32).toInt = expected ∧
    result.state.memory = AddressSpace.toMemory (installed compiler).space ∧
    result.state.rip = caller.returnAddress ∧
    result.state.registers .rsp = caller.stack + 8 ∧
    CallResources.Current (loadedCall compiler value).resource.call
      (loadedCall compiler value).resource.shared result.state

/-- Numeric expectations come from integer order alone. The actual-input
binding and execution/resource evidence come from the shared all-inputs
installed-call theorem, rather than from a synthetic code mapping. -/
private theorem numeric_result (compiler : Compiler) (value : BitVec 32) (expected : Int)
    (mathematics : WordMath.Signum value.toInt expected)
    (choices : ChoiceStream FlagChoices) : Returns compiler value expected choices := by
  obtain ⟨result, execution, correct, memory, returned, stack, current⟩ :=
    allInputsResult compiler value choices
  exact ⟨result, execution, initial_entry compiler value,
    WordMath.signum_unique correct mathematics, memory, returned, stack, current⟩

/-- The signed minimum is included: negation overflow is irrelevant to signum. -/
theorem signed_minimum (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    Returns compiler (BitVec.intMin 32) (-1) choices :=
  numeric_result compiler _ _ (by unfold WordMath.Signum; decide +kernel) choices

/-- Negative one must retain -1; replacing the arithmetic sign mask with a
logical shift or replacing OR with XOR would violate this observation. -/
theorem negative_one (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    Returns compiler (-1) (-1) choices :=
  numeric_result compiler _ _ (by unfold WordMath.Signum; decide +kernel) choices

theorem positive_one (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    Returns compiler 1 1 choices :=
  numeric_result compiler _ _ (by unfold WordMath.Signum; decide +kernel) choices

/-- Positive magnitude is discarded even at the largest signed low32 input. -/
theorem signed_maximum (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    Returns compiler 0x7fffffff 1 choices :=
  numeric_result compiler _ _ (by unfold WordMath.Signum; decide +kernel) choices

/-- Zero is admitted, executes and returns through the same caller resources
although the separate existential usefulness predicate excludes it. -/
theorem zero_is_admitted (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    PureCall.ResourcePre spec (bytes compiler) (resource compiler 0) (initial compiler 0) ∧
    ¬spec.useful (0 : BitVec 32) ∧ Returns compiler 0 0 choices := by
  refine ⟨pre compiler 0, ?_,
    numeric_result compiler _ _ (by unfold WordMath.Signum; decide +kernel) choices⟩
  change ¬((0 : BitVec 32).toInt < -1 ∨ 1 < (0 : BitVec 32).toInt)
  decide +kernel

#print axioms signed_minimum
#print axioms negative_one
#print axioms positive_one
#print axioms signed_maximum
#print axioms zero_is_admitted
end EDSL.Tests.SignumResources
#audit_edsl
