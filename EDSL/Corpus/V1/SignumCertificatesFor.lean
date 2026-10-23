/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumResources
import EDSL.PureCall.ELFCertificateFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Corpus.V1.SignumCertificatesFor
open X86

/-- Both complete named ELF artifacts meet the independent integer-order
signum contract under full-vector execution and the original current-resource
policy. All signed low32 values, including INT32_MIN, are admitted. The useful
INT32_MIN witness is at each artifact's actual selected address.

This neutral certificate fixes `Scalar32.signumSigned` through `SignumCode.spec`.
It supplies no objective-grader registration or corpus score claim. Stable
ordinary RAM, supplied logical authority, four-level canonical addresses,
alignment checking off, CET/IBT/shadow stacks off and no asynchronous
interference remain callable-target assumptions. Native CPU/Linux and
source/compiler correspondence are separate obligations. -/
def certificate (compiler : SignumCode.Compiler) :
    PureCall.ELFCertificateFor .flags SignumCode.spec
      (SignumWindows.file compiler) SignumWindows.name :=
  PureCall.ELFCertificateFor.ofCaller .flags SignumCode.spec
    (SignumWindows.input compiler) (SignumWindows.checked compiler)
    (SignumResources.semantics compiler)
    SignumResources.caller (SignumResources.fresh compiler)
    ELF.CallerResources.Stack.standard_facts (SignumResources.separate compiler)
    SignumResources.usefulValue (SignumCode.domain SignumResources.usefulValue)
    SignumResources.useful_value

#print axioms certificate
end EDSL.Corpus.V1.SignumCertificatesFor
#audit_edsl
