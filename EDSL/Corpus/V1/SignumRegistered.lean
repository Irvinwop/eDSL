/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CertificateFor
import EDSL.Corpus.V1.SignumCertificatesFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Corpus.V1.SignumRegistered
open X86

/-- Equality fixes the whole independent signed low32 signum task, including
its admission/resource policies and production flag-vector executor. -/
theorem registration : Grading.registry .signumSigned32 =
    ⟨.flags, Grading.ofReadOnlyFor .flags (PureCall.readOnlyTask Scalar32.signumSigned)⟩ := rfl

/-- Both exact frozen named ELF functions use the shared certificate adapter
and neutral signum certificate. All signed low32 inputs remain admitted.
Stable ordinary RAM, supplied logical authority, four-level canonical
addresses, alignment checking off, CET/IBT/shadow stacks off and no asynchronous
interference remain callable-target assumptions. Native CPU/Linux and
source/compiler correspondence, runtime packet integration and corpus
acceptance require separate validation. -/
def certificate (compiler : SignumCode.Compiler) :
    Corpus.CertificateFor .signumSigned32 (SignumWindows.file compiler) SignumWindows.name :=
  Corpus.CertificateFor.ofReadOnly .signumSigned32 .flags Scalar32.signumSigned registration
    (SignumCertificatesFor.certificate compiler)

/-- The registered claim covers the exact selected bytes and both complete
raw/current-resource domains, plus independent useful-domain witnesses. -/
theorem claim (compiler : SignumCode.Compiler) :
    Grading.RegisteredClaim .signumSigned32 (SignumCode.bytes compiler) :=
  (certificate compiler).registeredClaim

#print axioms registration
#print axioms certificate
#print axioms claim
end EDSL.Corpus.V1.SignumRegistered
#audit_edsl
