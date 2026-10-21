/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainResources.Frozen
import EDSL.OS.PlainCallAdmission64

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.PlainResources.Frozen
open X86 OS Grading.ConcurrentTask

/-- Candidate shape checking stays outside the generic resource provider and
outside independent Pre. Entire extents, including original GCC ENDBR64, use
the existing production checker and unchanged PlainWindows shape theorem. -/
def static (compiler : Compiler) : PlainCallAdmission64.StaticShapes (catalog compiler) where
  padding _ := V1.PlainWindows.padding compiler
  checked selected member := by
    simp only [catalog, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · cases same
      exact V1.PlainWindows.shape_checked compiler .loadAcquire
    · cases same
      exact V1.PlainWindows.shape_checked compiler .storeRelease

#print axioms static
#print axioms cohort
#print axioms pre
#print axioms closedPre
#print axioms full_image
#print axioms programSpace_eq
end EDSL.Corpus.PlainResources.Frozen

#audit_edsl
