/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CertificateFor
import EDSL.Corpus.V1.MultiplyCertificatesFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.MultiplyRegistered
open X86

/-- Equality fixes the independent natural-product specification, complete
admission/resource policies and production flag-vector executor together. -/
theorem registration : Grading.registry .multiplyModulo64 =
    ⟨.flags, Grading.ofReadOnlyFor .flags (PureCall.readOnlyTask MultiplyCode.spec)⟩ := rfl

/-- Both exact frozen named ELF functions use the same certificate adapter.
The trusted registry fixes their semantics; neither compiler chooses a model
or specification. Runtime packet/grader integration and corpus acceptance are
separate checks, so this theorem alone does not change published coverage. -/
def certificate (compiler : MultiplyCode.Compiler) :
    Corpus.CertificateFor .multiplyModulo64 (MultiplyWindows.file compiler) MultiplyWindows.name :=
  Corpus.CertificateFor.ofReadOnly .multiplyModulo64 .flags MultiplyCode.spec registration
    (MultiplyCertificatesFor.certificate compiler)

/-- The registered claim covers the exact selected bytes and both complete
raw/current-resource domains, plus independent useful-domain witnesses. -/
theorem claim (compiler : MultiplyCode.Compiler) :
    Grading.RegisteredClaim .multiplyModulo64 (MultiplyCode.bytes compiler) :=
  (certificate compiler).registeredClaim

#print axioms registration
#print axioms certificate
#print axioms claim
end EDSL.Corpus.V1.MultiplyRegistered
#audit_edsl
