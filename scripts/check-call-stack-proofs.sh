#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $# != 5 ]]; then
    echo 'usage: scripts/check-call-stack-proofs.sh OUTPUT GCC_SAME GCC_SEPARATE CLANG_SAME CLANG_SEPARATE' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=$1
shift
mkdir -p "$output"
output=$(cd "$output" && pwd)
# Save complete inputs before building. Checked pipelines reject enumeration
# failures instead of silently producing an incomplete source snapshot.
find EDSL tests/fixtures/CallStack tests/fixtures/CallStackPrograms.lean -type f -name '*.lean' -print0 |
    sort -z > "$output/lean-inputs.list0"
mapfile -d '' -t lean_inputs < "$output/lean-inputs.list0"
if [[ ${#lean_inputs[@]} == 0 ]]; then
    echo 'No proof sources were enumerated' >&2
    exit 1
fi
tar -czf "$output/proof-sources.tar.gz" -- "${lean_inputs[@]}" EDSL.lean lakefile.lean \
    lake-manifest.json lean-toolchain scripts/check-call-stack-proofs.sh \
    scripts/check-call-stack-grading.sh Tools/Grade/CallStack.lean Tools/Grade/Function.lean Tools/ProofExport.lean tests/CallStack.lean
sha256sum -- "${lean_inputs[@]}" EDSL.lean lakefile.lean lake-manifest.json lean-toolchain \
    scripts/check-call-stack-proofs.sh scripts/check-call-stack-grading.sh \
    Tools/Grade/CallStack.lean Tools/Grade/Function.lean Tools/ProofExport.lean tests/CallStack.lean > "$output/proof-input-SHA256SUMS"
lake build tests.fixtures.CallStack.CoveredAudit tests.fixtures.CallStack.FoundationAudit \
    tests.fixtures.CallStack.Inline.Accounting > "$output/build.log" 2>&1
lake env lean -DwarningAsError=true tests/CallStack.lean > "$output/audit.log" 2>&1
names=(GccSame GccSeparate ClangSame ClangSeparate)
profiles=(gccSame gccSeparate clangSame clangSeparate)
entries=(5 0 5 0)
costs=(5 7 7 7)
# Lean's local module loader resolves an explicit object through LEAN_PATH.
# These paths contain data read by od, never commands or generated tactic code.
source_file="$output/CallStackObserved.lean"
cat > "$source_file" <<'LEAN'
import tests.fixtures.CallStack.CoveredAudit
import tests.fixtures.CallStack.FoundationAudit
import tests.fixtures.CallStack.Inline.Accounting
import EDSL.Audit
set_option warningAsError true
namespace EDSL.CallStack.Observed
open X86 OS
LEAN
for index in 0 1 2 3; do
    artifact=$1
    shift
    {
      printf 'def bytes%s : List Byte := [' "${names[index]}"
      od -An -v -tu1 -- "$artifact" | awk '
      { for (i=1;i<=NF;i++) { if (seen++) printf ","; printf "%s",$i } }
      END { printf "]\n" }'
      cat <<LEAN
example : Compiler.bytes .${profiles[index]} = bytes${names[index]} := by decide
/-- The whole observed linked text and its selected entry instantiate the
same universal raw-execution and current-resource theorem. -/
theorem contract${names[index]} {resource : Resources} {initial : State}
    (pre : ResourcePre ⟨bytes${names[index]}, ${entries[index]}⟩ resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      CallReturn.run choices ${costs[index]} initial = .ok result ∧
      StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved result ∧
      StackFrame.Current resource.frame evolved result.state ∧
      StackFrame.Preservation resource.frame resource.shared evolved ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = ${costs[index]} ∧
      result.reads = Compiler.reads .${profiles[index]} resource.frame.top :=
  Compiler.evaluated .${profiles[index]} pre choices
#print axioms EDSL.CallStack.Observed.contract${names[index]}
LEAN
    } >> "$source_file"
    sha256sum -- "$artifact" >> "$output/extraction-SHA256SUMS"
done
printf 'end EDSL.CallStack.Observed\n#audit_edsl\n' >> "$source_file"
lake env lean -R "$output" -DwarningAsError=true -o "$output/CallStackObserved.olean" "$source_file" \
    > "$output/observed-proof.log" 2>&1
# Fresh replay checks the generated theorem and all transitive imported proofs,
# including admission, code coverage, the independent clients and cost bound.
proof_path="$output:$(lake env printenv LEAN_PATH)"
lake env env LEAN_PATH="$proof_path" leanchecker --fresh --verbose CallStackObserved > "$output/fresh-kernel.log" 2>&1
printf 'formal=PASS whole_texts=4 universal_input=true typed_os_execution=true fresh_kernel=true\n' > "$output/result.txt"
