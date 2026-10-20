/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteScan
import EDSL.Grading.IndexSearch
import EDSL.Grading.ByteComparison
import EDSL.Grading.ByteEquality

set_option autoImplicit false
set_option warningAsError true

/-!
Fixed independent buffer tasks for the represented sequential read-only x86
callable model. This family leaves the existing scalar TaskID and registry
unchanged. Its types alone provide no certificate, grader entry or corpus credit.
-/

namespace EDSL.Grading.BufferTask
open X86

def model : String := "sequential-read-only-x86-buffer-callable-v1"

/-- Trusted mathematical identities, independent of source languages, symbol
names and candidate instruction shapes. Extending this enum and its definition
below is a trusted registration change, not a candidate proof parameter. -/
inductive TaskID where
  | firstBoundedNulLength
  | memchrIndex
  | linearSearchU32
  | lexicographicBytes
  /-- Exact list equality as canonical low8 zero/one; upper56 RAX is free. -/
  | equalBytes
  deriving DecidableEq, Repr

/-- A generic BufferCall.Spec record cannot enforce independence of its fields.
This trusted definition fixes the entire input type, arguments, snapshots,
domain, result and usefulness to independently defined mathematics. Candidates
cannot supply a weaker Spec or select a different contract by naming a symbol. -/
def registeredSpec : TaskID → BufferCall.Spec
  | .firstBoundedNulLength => ByteScan.spec
  | .memchrIndex => IndexSearch.byteSpec
  | .linearSearchU32 => IndexSearch.u32Spec
  | .lexicographicBytes => ByteComparison.spec
  | .equalBytes => ByteEquality.spec

/-- Reuse the exact current-resource adapter and its versioned
sequentialReadOnlyX86CallableV1 profile, including original caller authority,
whole-memory frames and every-prefix read permissions. Stable ordinary RAM,
modeled ownership and absent asynchronous interference are environmental
assumptions; no physical CPU, Linux/GNU, fairness or cost-minimum claim is made. -/
def registered (id : TaskID) : ReadOnlyTask :=
  BufferCall.readOnlyTask (registeredSpec id)

abbrev SemanticClaim (id : TaskID) (bytes : List Byte) : Prop :=
  ReadOnlySemanticClaim (registered id) bytes

/-- The trusted task identity and exact bytes fix the complete proof type.
Universal behavior and useful present-domain evidence are separate obligations;
neither decoder acceptance nor a future successful run is an admission premise. -/
def Claim (id : TaskID) (bytes : List Byte) : Prop :=
  SemanticClaim id bytes ∧ ReadOnlyNonvacuous (registered id) bytes

end EDSL.Grading.BufferTask
