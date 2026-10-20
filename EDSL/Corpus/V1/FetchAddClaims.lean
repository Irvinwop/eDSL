/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddBatch64.Certificate
import EDSL.Corpus.ConcurrentCertificate
import EDSL.Corpus.V1.FetchAddBodies

set_option warningAsError true
set_option autoImplicit false

/-!
The fixed concurrent contract for both frozen full64 fetch-add symbol windows,
including GCC's original ENDBR64 under the explicit CET-off target profile.
Loaded-resource and overlapping-execution witnesses remain separate certificate
obligations. These claims alone do not register corpus credit.
-/

namespace EDSL.Corpus.V1.FetchAddClaims
open X86 OS

/-- Universal independent contract at each actual ELF symbol address and for
its entire unchanged byte extent. No compiler-specific execution proof. -/
theorem claim (compiler : FetchAddWindows.Compiler) :
    Grading.ConcurrentTask.FetchAdd64.Claim
      (Concurrent.Image (FetchAddWindows.input compiler)) :=
  FetchAddBatch64.checked_claim _ (FetchAddBodies.padding compiler)
    (FetchAddBodies.shape_checked compiler)

#print axioms claim
end EDSL.Corpus.V1.FetchAddClaims

#audit_edsl
