/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.MultiplyResources
import EDSL.PureCall.ELFCertificateFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.MultiplyCertificatesFor
open X86

/-- Both complete named ELF artifacts meet the independently defined modular
product contract under full-vector execution and the original current-resource
policy. The useful witness is at each artifact's actual selected address.

This neutral certificate fixes its mathematical specification here. It does
not constitute registration in the objective grader or increase corpus scores.
The callable target's stable ordinary RAM, supplied logical authority, disabled
CET/shadow stacks and absence of asynchronous interference remain assumptions;
native CPU/Linux and source/compiler correspondence are separate obligations. -/
def certificate (compiler : MultiplyCode.Compiler) :
    PureCall.ELFCertificateFor .flags MultiplyCode.spec
      (MultiplyWindows.file compiler) MultiplyWindows.name :=
  PureCall.ELFCertificateFor.ofCaller .flags MultiplyCode.spec
    (MultiplyWindows.input compiler) (MultiplyWindows.checked compiler)
    (MultiplyResources.semantics compiler)
    MultiplyResources.caller (MultiplyResources.fresh compiler)
    ELF.CallerResources.Stack.standard_facts (MultiplyResources.separate compiler)
    MultiplyResources.usefulValue (MultiplyCode.domain MultiplyResources.usefulValue)
    MultiplyResources.useful_value

#print axioms certificate
end EDSL.Corpus.V1.MultiplyCertificatesFor
#audit_edsl
