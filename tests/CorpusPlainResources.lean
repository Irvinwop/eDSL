/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainResources
import EDSL.Corpus.PlainExecution
import EDSL.Corpus.V1.PlainClaims

/-!
End-to-end composition of unchanged complete compiler ELF files, actual managed
resource construction, independent admission and the shared full contract.
The final-state assertion concerns every original ELF cell and permission;
the execution includes real issue and publication schedules. Data and counters
remain arbitrary. These clients impose no overlap or selected read-from edge,
so they do not establish useful-population certificates or corpus credit.
-/

set_option autoImplicit false

namespace EDSL.Tests.CorpusPlainResources
open X86 OS Grading.ConcurrentTask.Plain64 Corpus

theorem mixed_image_survives (compiler : V1.PlainInputs.Compiler)
    (old storeValue loadArgument : Word) (writerCounter readerCounter : Nat)
    (choices : Nat → Nat → Bool) :
    let batch := PlainResources.Inputs.mixed compiler old storeValue loadArgument
      writerCounter readerCounter 101 202
    ∃ execution : Plain.Execution batch choices,
      ∀ address original, batch.loaded.space.cells address = some original →
        execution.drained.1.world.legacy.shared.resources.space.cells address = some original := by
  dsimp only
  obtain ⟨execution⟩ := Plain.LoadedBatch.execute
    (PlainResources.Inputs.mixed compiler old storeValue loadArgument
      writerCounter readerCounter 101 202)
    (by simpa only [V1.PlainInputs.images_catalog] using V1.PlainClaims.cohort compiler) choices
  exact ⟨execution, fun _ _ live => execution.retainedImage live⟩

/-- Singleton catalog restriction uses the real homogeneous inputs, then the
same machine proof completes and closes either operation in either full ELF. -/
theorem homogeneous_image_survives (compiler : V1.PlainInputs.Compiler) (kind : Kind)
    (old valueA valueB : Word) (counterA counterB : Nat) (choices : Nat → Nat → Bool) :
    let batch := PlainResources.Inputs.homogeneous compiler kind old valueA valueB
      counterA counterB 303 404
    ∃ execution : Plain.Execution batch choices,
      ∀ address original, batch.loaded.space.cells address = some original →
        execution.drained.1.world.legacy.shared.resources.space.cells address = some original := by
  dsimp only
  obtain ⟨execution⟩ := Plain.LoadedBatch.execute
    (PlainResources.Inputs.homogeneous compiler kind old valueA valueB counterA counterB 303 404)
    (V1.PlainClaims.named compiler kind) choices
  exact ⟨execution, fun _ _ live => execution.retainedImage live⟩

end EDSL.Tests.CorpusPlainResources

#print axioms EDSL.Tests.CorpusPlainResources.mixed_image_survives
#print axioms EDSL.Tests.CorpusPlainResources.homogeneous_image_survives
#audit_edsl
