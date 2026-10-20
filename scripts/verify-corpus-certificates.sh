#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# This gate checks synthetic, project-owned frozen inputs. Native tools below
# generate/compare mutations; only Lean's proofs and fresh checker supply proof
# evidence. No input ELF is executed.
# Native dependencies include GNU binutils readelf (section metadata), jq,
# GNU coreutils, awk, find, sort, git and util-linux flock; no rg is required.
set -euo pipefail
export LC_ALL=C
umask 077

full_project=false
case "$#:${1:-}" in
    0:) ;;
    1:--full-project) full_project=true ;;
    1:--help)
        echo 'usage: scripts/verify-corpus-certificates.sh [--full-project]'
        echo 'Builds twenty scalar, two managed concurrent fetch-add, two bounded byte-scan, four first-match search and two byte-comparison certificates, audits axioms and checks file binding.'
        echo 'Default: fresh-replays corpus.Certify. --full-project: also builds the full catalogue and verification, unary, popcount, average, parity, rotation, low-byte and CFG-profile tests; fresh-replays them together.'
        exit 0 ;;
    *) echo 'usage: scripts/verify-corpus-certificates.sh [--full-project]' >&2; exit 2 ;;
esac

cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
archive=$root/artifacts/corpus-certificates
mkdir -p "$archive/runs"
output=$(mktemp -d "$archive/runs/run.$(date -u +%Y%m%dT%H%M%SZ).XXXXXXXX")
mkdir -p "$output/commands" "$output/lib/corpus" "$output/source" "$output/mutations"
printf '%s\n' "$output" > "$archive/LATEST"
printf 'Corpus certificate gate receipts: %s\n' "$output" >&2

# Every Lean/Lake/checker invocation takes its own lock. In particular, there is
# no outer lock while native checks, shell controls or hashing run.
lean_lock=(env "PATH=${ELAN_HOME:-$HOME/.elan}/bin:$PATH" LEAN_NUM_THREADS=1
    flock /tmp/edsl-lean-build.lock)
search_path=$output/lib:$root/.lake/build/lib/lean
lean_env=("${lean_lock[@]}" lake env env "LEAN_PATH=$search_path")
cli=("${lean_env[@]}" lean -DwarningAsError=true --run corpus/Certify.lean)
gcc_file=corpus/v1/gcc/final.elf
clang_file=corpus/v1/clang/final.elf
stage=setup
complete=false
gate_scope=corpus-cli
fresh_target=corpus.Certify
fresh_label=fresh-corpus
if [[ $full_project == true ]]; then
    gate_scope=full-project-and-corpus-cli
    fresh_target=CorpusFullReplay
    fresh_label=fresh-project-and-corpus
fi
printf '%s\n' "$gate_scope" > "$output/scope.txt"
printf '%s\n' "$fresh_target" > "$output/fresh-target.txt"
printf '%s\n' "$fresh_label" > "$output/fresh-receipt-label.txt"

record() {
    local name=$1 status=0
    shift
    stage=$name
    {
        printf 'cd %q\n' "$root"
        printf '%q ' "$@"
        printf '\n'
    } > "$output/commands/$name.command"
    printf '%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$output/commands/$name.started"
    printf 'corpus certificates: %s\n' "$name" >&2
    "$@" > "$output/commands/$name.stdout" 2> "$output/commands/$name.stderr" || status=$?
    printf '%s\n' "$status" > "$output/commands/$name.exit"
    printf '%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$output/commands/$name.finished"
    printf '%s\t%s\n' "$name" "$status" >> "$output/commands.tsv"
    return "$status"
}

# Include new, untracked public sources as well as tracked ones. Recreate this
# inventory afterwards so additions/deletions cannot escape the stability gate.
source_hash_command='git ls-files --cached --others --exclude-standard -z --
    "*.lean" "*.sh" "*.c" "*.cc" "*.cpp" "*.h" "*.hpp" "*.S" "*.s" "*.ll"
    lean-toolchain lakefile.lean lakefile.toml lake-manifest.json AGENTS.md "corpus/v1/*" |
    sort -zu | xargs -0 -r sha256sum --'
# Keep the command one shell pipeline; newlines above are argument separators.
source_hash_command=${source_hash_command//$'\n'/ }
printf -v module_hash_command 'find .lake/build/lib/lean %q -type f \( -name "*.olean" -o -name "*.olean.private" -o -name "*.olean.server" \) -print0 | sort -z | xargs -0 -r sha256sum --' "$output/lib"
printf -v receipt_hash_command 'find %q -type f ! -path %q ! -path %q -print0 | sort -z | xargs -0 -r sha256sum --' \
    "$output" "$output/commands/receipt-manifest.*" "$output/commands.tsv"

finish() {
    local status=$? failed_stage=$stage stability=0
    trap - EXIT
    set +e
    if [[ -f $output/source-before.sha256 ]]; then
        record source-after bash -o pipefail -c "$source_hash_command" || stability=1
        record source-manifest-stable cmp -- "$output/source-before.sha256" \
            "$output/commands/source-after.stdout" || stability=1
        record source-content-stable sha256sum --check "$output/source-before.sha256" || stability=1
    else
        stability=1
    fi
    if [[ -f $output/frozen-before.sha256 ]]; then
        record frozen-after sha256sum -- "$gcc_file" "$clang_file" || stability=1
        record frozen-manifest-stable cmp -- "$output/frozen-before.sha256" \
            "$output/commands/frozen-after.stdout" || stability=1
        record frozen-content-stable sha256sum --check "$output/frozen-before.sha256" || stability=1
    else
        stability=1
    fi
    if [[ -f $output/modules-before.sha256 ]]; then
        record modules-after bash -o pipefail -c "$module_hash_command" || stability=1
        record modules-stable cmp -- "$output/modules-before.sha256" \
            "$output/commands/modules-after.stdout" || stability=1
    fi
    if [[ -f $output/gate-inputs.sha256 ]]; then
        record gate-inputs-stable sha256sum --check "$output/gate-inputs.sha256" || stability=1
    fi
    if [[ $full_project == true ]]; then
        if [[ -f $output/cli-binaries-before.sha256 ]]; then
            record cli-binaries-stable sha256sum --check "$output/cli-binaries-before.sha256" || stability=1
        else
            stability=1
        fi
    fi
    if (( stability != 0 )); then
        [[ $status -ne 0 ]] || failed_stage=final-stability
        status=1
    fi
    if [[ $complete != true && $status -eq 0 ]]; then
        failed_stage=incomplete-gate
        status=1
    fi
    printf '%s\n' "$status" > "$output/exit"
    if [[ $status -eq 0 ]]; then
        cat > "$output/READY.md" <<EOF
Certificate gate passed for the inputs recorded in source-before.sha256 and frozen-before.sha256.
Scope: $gate_scope.
Build, private CLI compilation, imported-project axiom audit, actual fresh kernel replay,
deterministic real-file JSON, valid flag forms and synthetic rejection controls passed.
report.json concerns the recorded model assumptions only. No ELF was executed.
The leanchecker --fresh target was $fresh_target; receipts: commands/$fresh_label.*.
Every command has exact stdout, stderr, status and arguments in commands/.
EOF
        if [[ $full_project == true ]]; then
            cat >> "$output/READY.md" <<'EOF'
The stored private source/CorpusFullReplay.lean imports EDSL.All, corpus.Certify and reusable verification regression modules.
Its compiled aggregate was replayed once in a fresh environment covering both closures.
The axiom audit also imports that aggregate, including all root EDSL declarations.
EOF
        else
            cat >> "$output/READY.md" <<'EOF'
The fresh replay covers corpus.Certify only; root EDSL replay is not claimed.
EOF
        fi
    else
        cat > "$output/BLOCKERS.md" <<EOF
Gate did not pass. Stage at failure: $failed_stage; gate exit: $status.
Final source/frozen/module/input stability failure flag: $stability.
Inspect commands/$failed_stage.{command,stdout,stderr,exit} when present and commands.tsv.
No certificate score or full replay success is claimed by this run.
Missing certificate APIs must be supplied by their owners; this gate supplies no stubs.
EOF
    fi
    # Hash the closed evidence files; exclude this command's own receipts and
    # the index it still appends to. Never remove failed attempts or mutations.
    record receipt-manifest bash -o pipefail -c "$receipt_hash_command"
    local manifest_status=$?
    if (( manifest_status != 0 )); then
        status=1
        printf '%s\n' "$status" > "$output/exit"
        rm -f -- "$output/READY.md"
        printf 'Evidence manifest could not be completed.\n' >> "$output/BLOCKERS.md"
    fi
    if [[ $status -eq 0 ]]; then
        printf 'Corpus certificate gate passed: %s\n' "$output"
    else
        printf 'Corpus certificate gate failed at %s; receipts: %s\n' "$failed_stage" "$output" >&2
    fi
    exit "$status"
}
trap finish EXIT

record source-before bash -o pipefail -c "$source_hash_command"
record save-source-hashes cp -- "$output/commands/source-before.stdout" "$output/source-before.sha256"
record frozen-before sha256sum -- "$gcc_file" "$clang_file"
record save-frozen-hashes cp -- "$output/commands/frozen-before.stdout" "$output/frozen-before.sha256"
record frozen-seal sha256sum --check corpus/v1/SHA256SUMS
record git-head git rev-parse HEAD
record git-status git status --short
record toolchain cat lean-toolchain
record readelf-version readelf --version
record arithmetic-certificate-api test -f EDSL/Corpus/V1/Arithmetic.lean
record clamp-certificate-api test -f EDSL/Corpus/V1/Clamps.lean
record concurrent-certificate-api test -f EDSL/Corpus/V1/FetchAddCertificates.lean
record buffer-certificate-api test -f EDSL/Corpus/V1/ByteScanCertificates.lean
record index-search-certificate-api test -f EDSL/Corpus/V1/IndexSearchCertificates.lean
record byte-comparison-certificate-api test -f EDSL/Corpus/V1/ByteComparisonCertificates.lean
record unary-certificate-api test -f EDSL/Corpus/V1/UnaryCertificates.lean
record popcount-certificate-api test -f EDSL/Corpus/V1/PopcountCertificates.lean
record average-certificate-api test -f EDSL/Corpus/V1/AverageCertificates.lean
record parity-certificate-api test -f EDSL/Corpus/V1/ParityCertificates.lean
record rotation-certificate-api test -f EDSL/Corpus/V1/RotationCertificates.lean
record lean-version "${lean_lock[@]}" lean --version

if [[ $full_project == true ]]; then
    # This is a stored private module, not a source-elaboration success relabeled
    # as fresh replay. --root below sets its module name; LEAN_PATH finds its
    # olean in the distinct private lib alongside the private corpus.Certify.
    cat > "$output/source/CorpusFullReplay.lean" <<'LEAN'
import EDSL.All
import corpus.Certify
import tests.VerificationImports
import tests.VerifyFunction
import tests.ELFCertificate
import tests.ELFFunctionSymbol
import tests.ELFFunctionCandidate
import tests.ELFStackCaller
import tests.ELFFunctionBounds
import tests.SequentialUnary
import tests.UnaryBodies
import tests.CorpusUnaryResources
import tests.GradingUnary
import tests.SequentialCounter32
import tests.SequentialDisplacement
import tests.VCGenCompactLoop
import tests.PopcountBodies
import tests.CorpusPopcountResources
import tests.GradingPopcount
import tests.WordMathAverage
import tests.SequentialShiftOne
import tests.ShiftOneAudit
import tests.AverageBodies
import tests.AverageResources
import tests.GradingAverage
import tests.SequentialParityISA
import tests.ParityISAAudit
import tests.ParityBodies
import tests.ParityResources
import tests.GradingParity
import tests.SequentialRotate
import tests.RotateAudit
import tests.RotationBodies
import tests.RotationResources
import tests.GradingRotation
import tests.SequentialLow8
import tests.Low8Audit
import tests.ByteEquality
import tests.SequentialByteComparePadding
import tests.ByteComparePaddingAudit
import tests.CFGProfiles
import tests.VCGenScratchFrame
LEAN
    printf 'import CorpusFullReplay\n' > "$output/Audit.lean"
else
    printf 'import corpus.Certify\n' > "$output/Audit.lean"
fi
cat >> "$output/Audit.lean" <<'LEAN'
import EDSL.Audit

-- Independently require the promised eight compiler/operation instances, so a
-- future replacement of acceptedCertificates by a weaker proposition fails.
example :
    Nonempty (EDSL.Corpus.Certificate (EDSL.Corpus.Comparison.taskID .minimum)
      (EDSL.Corpus.V1.Comparisons.file .defaultGCC) (EDSL.Corpus.Comparison.name .minimum)) ∧
    Nonempty (EDSL.Corpus.Certificate (EDSL.Corpus.Comparison.taskID .maximum)
      (EDSL.Corpus.V1.Comparisons.file .defaultGCC) (EDSL.Corpus.Comparison.name .maximum)) ∧
    Nonempty (EDSL.Corpus.Certificate .addModulo64
      (EDSL.Corpus.V1.ArithmeticWindows.file .defaultGCC)
      EDSL.Corpus.V1.ArithmeticWindows.name) ∧
    Nonempty (EDSL.Corpus.Certificate .clampSigned32
      (EDSL.Corpus.V1.Clamps.file .defaultGCC) EDSL.Corpus.V1.Clamps.name) ∧
    Nonempty (EDSL.Corpus.Certificate (EDSL.Corpus.Comparison.taskID .minimum)
      (EDSL.Corpus.V1.Comparisons.file .defaultClang) (EDSL.Corpus.Comparison.name .minimum)) ∧
    Nonempty (EDSL.Corpus.Certificate (EDSL.Corpus.Comparison.taskID .maximum)
      (EDSL.Corpus.V1.Comparisons.file .defaultClang) (EDSL.Corpus.Comparison.name .maximum)) ∧
    Nonempty (EDSL.Corpus.Certificate .addModulo64
      (EDSL.Corpus.V1.ArithmeticWindows.file .defaultClang)
      EDSL.Corpus.V1.ArithmeticWindows.name) ∧
    Nonempty (EDSL.Corpus.Certificate .clampSigned32
      (EDSL.Corpus.V1.Clamps.file .defaultClang) EDSL.Corpus.V1.Clamps.name) :=
  EDSL.Corpus.Reporting.acceptedCertificates

-- Require the fixed independent concurrent contract for each complete file,
-- rather than trusting the report's operation/model/proof strings.
example :
    Nonempty (EDSL.Corpus.Concurrent.FetchAddCertificate
      (EDSL.Corpus.V1.FetchAddWindows.file .defaultGCC)
      EDSL.Corpus.V1.FetchAddWindows.name) ∧
    Nonempty (EDSL.Corpus.Concurrent.FetchAddCertificate
      (EDSL.Corpus.V1.FetchAddWindows.file .defaultClang)
      EDSL.Corpus.V1.FetchAddWindows.name) :=
  EDSL.Corpus.Reporting.acceptedConcurrentCertificates

-- Require the fixed independent bounded-NUL contract for each complete file.
example :
    Nonempty (EDSL.Corpus.Buffer.Certificate .firstBoundedNulLength
      (EDSL.Corpus.V1.ByteScanWindows.file .defaultGCC)
      EDSL.Corpus.V1.ByteScanWindows.name) ∧
    Nonempty (EDSL.Corpus.Buffer.Certificate .firstBoundedNulLength
      (EDSL.Corpus.V1.ByteScanWindows.file .defaultClang)
      EDSL.Corpus.V1.ByteScanWindows.name) :=
  EDSL.Corpus.Reporting.acceptedBufferCertificates
example (compiler : EDSL.Corpus.V1.ByteScanWindows.Compiler) :
    (EDSL.Corpus.V1.ByteScanCertificates.certificate compiler).input =
      EDSL.Corpus.V1.ByteScanWindows.input compiler := rfl
example (compiler : EDSL.Corpus.V1.ByteScanWindows.Compiler) :
    EDSL.Corpus.V1.ByteScanWindows.file compiler =
      EDSL.Corpus.V1.Comparisons.file compiler := rfl

-- Require both fixed independent search tasks for each complete file; an
-- unrelated buffer task or a candidate-selected Spec cannot supply this type.
example :
    Nonempty (EDSL.Corpus.Buffer.Certificate .memchrIndex
      (EDSL.Corpus.V1.IndexSearchWindows.file .defaultGCC)
      (EDSL.Corpus.V1.IndexSearchWindows.name .byte)) ∧
    Nonempty (EDSL.Corpus.Buffer.Certificate .linearSearchU32
      (EDSL.Corpus.V1.IndexSearchWindows.file .defaultGCC)
      (EDSL.Corpus.V1.IndexSearchWindows.name .u32)) ∧
    Nonempty (EDSL.Corpus.Buffer.Certificate .memchrIndex
      (EDSL.Corpus.V1.IndexSearchWindows.file .defaultClang)
      (EDSL.Corpus.V1.IndexSearchWindows.name .byte)) ∧
    Nonempty (EDSL.Corpus.Buffer.Certificate .linearSearchU32
      (EDSL.Corpus.V1.IndexSearchWindows.file .defaultClang)
      (EDSL.Corpus.V1.IndexSearchWindows.name .u32)) :=
  EDSL.Corpus.Reporting.acceptedIndexSearchCertificates
example (compiler : EDSL.Corpus.V1.IndexSearchWindows.Compiler)
    (operation : EDSL.Corpus.V1.IndexSearchWindows.Operation) :
    (EDSL.Corpus.V1.IndexSearchCertificates.certificate compiler operation).input =
      EDSL.Corpus.V1.IndexSearchWindows.input compiler operation := rfl
example (compiler : EDSL.Corpus.V1.IndexSearchWindows.Compiler) :
    EDSL.Corpus.V1.IndexSearchWindows.file compiler =
      EDSL.Corpus.V1.Comparisons.file compiler := rfl

-- Require the registered unsigned lexicographic task, exact complete files and
-- name. Report labels and a candidate-selected Spec cannot supply this type.
example :
    Nonempty (EDSL.Corpus.Buffer.Certificate .lexicographicBytes
      (EDSL.Corpus.V1.Comparisons.file .defaultGCC)
      EDSL.Corpus.V1.ByteComparisonWindows.name) ∧
    Nonempty (EDSL.Corpus.Buffer.Certificate .lexicographicBytes
      (EDSL.Corpus.V1.Comparisons.file .defaultClang)
      EDSL.Corpus.V1.ByteComparisonWindows.name) :=
  EDSL.Corpus.Reporting.acceptedByteComparisonCertificates

-- Require both registry-owned unary contracts at both exact complete files.
example :
    Nonempty (EDSL.Corpus.Certificate .absSigned32
      (EDSL.Corpus.V1.UnaryWindows.file .defaultGCC)
      (EDSL.Corpus.V1.UnaryWindows.name .absSigned32)) ∧
    Nonempty (EDSL.Corpus.Certificate .byteSwap64
      (EDSL.Corpus.V1.UnaryWindows.file .defaultGCC)
      (EDSL.Corpus.V1.UnaryWindows.name .byteSwap64)) ∧
    Nonempty (EDSL.Corpus.Certificate .absSigned32
      (EDSL.Corpus.V1.UnaryWindows.file .defaultClang)
      (EDSL.Corpus.V1.UnaryWindows.name .absSigned32)) ∧
    Nonempty (EDSL.Corpus.Certificate .byteSwap64
      (EDSL.Corpus.V1.UnaryWindows.file .defaultClang)
      (EDSL.Corpus.V1.UnaryWindows.name .byteSwap64)) :=
  EDSL.Corpus.Reporting.acceptedUnaryCertificates

-- Require the whole independent loop contract at both exact final files.
example :
    Nonempty (EDSL.Corpus.Certificate .populationCount64
      (EDSL.Corpus.V1.PopcountWindows.file .defaultGCC)
      EDSL.Corpus.V1.PopcountWindows.name) ∧
    Nonempty (EDSL.Corpus.Certificate .populationCount64
      (EDSL.Corpus.V1.PopcountWindows.file .defaultClang)
      EDSL.Corpus.V1.PopcountWindows.name) :=
  EDSL.Corpus.Reporting.acceptedPopcountCertificates

-- Fix the complete row-08 artifact identities and registry-owned average task;
-- report text cannot substitute a wrapped-sum or candidate-selected contract.
example :
    Nonempty (EDSL.Corpus.Certificate .average64
      (EDSL.Corpus.V1.AverageWindows.file .defaultGCC)
      EDSL.Corpus.V1.AverageWindows.name) ∧
    Nonempty (EDSL.Corpus.Certificate .average64
      (EDSL.Corpus.V1.AverageWindows.file .defaultClang)
      EDSL.Corpus.V1.AverageWindows.name) :=
  EDSL.Corpus.Reporting.acceptedAverageCertificates
example (compiler : EDSL.Corpus.V1.AverageCode.Compiler) :
    (EDSL.Corpus.V1.AverageCertificates.certificate compiler).input =
      EDSL.Corpus.V1.AverageWindows.input compiler := by
  cases compiler <;> rfl
example (compiler : EDSL.Corpus.V1.AverageCode.Compiler) :
    EDSL.Corpus.V1.AverageWindows.file compiler =
      EDSL.Corpus.V1.Comparisons.file compiler := rfl

-- Pin the independent registered parity contract to the same complete files
-- read by the CLI and the literal full row-12 symbol name. An alias, report
-- string, different task or selected code window cannot satisfy this type.
example :
    Nonempty (EDSL.Corpus.Certificate .parity64
      (EDSL.Corpus.V1.Comparisons.file .defaultGCC)
      [99,95,112,97,114,105,116,121,95,108,111,111,112]) ∧
    Nonempty (EDSL.Corpus.Certificate .parity64
      (EDSL.Corpus.V1.Comparisons.file .defaultClang)
      [99,95,112,97,114,105,116,121,95,108,111,111,112]) :=
  EDSL.Corpus.Reporting.acceptedParityCertificates
example (compiler : EDSL.Corpus.V1.ParityCode.Compiler) :
    (EDSL.Corpus.V1.ParityCertificates.certificate compiler).input =
      EDSL.Corpus.V1.ParityWindows.input compiler := by
  cases compiler <;> rfl
example (compiler : EDSL.Corpus.V1.ParityCode.Compiler) :
    EDSL.Corpus.V1.ParityWindows.file compiler =
      EDSL.Corpus.V1.Comparisons.file compiler := rfl

-- The final ELF/name and registry-owned task are independent of report labels.
example :
    Nonempty (EDSL.Corpus.Certificate .rotateLeft64
      (EDSL.Corpus.V1.Comparisons.file .defaultGCC)
      [99,95,114,111,116,108,54,52]) ∧
    Nonempty (EDSL.Corpus.Certificate .rotateLeft64
      (EDSL.Corpus.V1.Comparisons.file .defaultClang)
      [99,95,114,111,116,108,54,52]) :=
  EDSL.Corpus.Reporting.acceptedRotationCertificates
example (compiler : EDSL.Corpus.V1.RotationCode.Compiler) :
    (EDSL.Corpus.V1.RotationCertificates.certificate compiler).input =
      EDSL.Corpus.V1.RotationWindows.input compiler := by
  cases compiler <;> rfl
example (compiler : EDSL.Corpus.V1.RotationCode.Compiler) :
    EDSL.Corpus.V1.RotationWindows.file compiler =
      EDSL.Corpus.V1.Comparisons.file compiler := rfl

-- Count actual retired instructions for arbitrary values, counts and choices.
example (compiler : EDSL.Corpus.V1.RotationCode.Compiler)
    {input : EDSL.PureCall.Invocation EDSL.Corpus.V1.RotationCode.spec}
    {initial : EDSL.X86.State}
    (pre : EDSL.PureCall.Pre EDSL.Corpus.V1.RotationCode.spec
      (EDSL.Corpus.V1.RotationCode.bytes compiler) input initial)
    {choices : EDSL.X86.Sequential.Choices} {result : EDSL.X86.Sequential.Result}
    (execution : EDSL.X86.Sequential.Executes choices initial result) :
    result.instructions = (match compiler with | .defaultGCC => 5 | .defaultClang => 4) := by
  have observed := EDSL.Corpus.V1.RotationBodies.observations compiler pre execution
  cases compiler <;> exact observed.2.2.1

-- These literal counts are conclusions for arbitrary admitted input pairs and
-- actual decoded execution, not fixture assignments or graph-size assertions.
example (compiler : EDSL.Corpus.V1.AverageCode.Compiler)
    {input : EDSL.PureCall.Invocation EDSL.Corpus.V1.AverageCode.spec}
    {initial : EDSL.X86.State}
    (pre : EDSL.PureCall.Pre EDSL.Corpus.V1.AverageCode.spec
      (EDSL.Corpus.V1.AverageCode.bytes compiler) input initial)
    {choices : EDSL.X86.Sequential.Choices} {result : EDSL.X86.Sequential.Result}
    (execution : EDSL.X86.Sequential.Executes choices initial result) :
    result.instructions = (match compiler with | .defaultGCC => 7 | .defaultClang => 6) := by
  have observed := EDSL.Corpus.V1.AverageBodies.observations compiler pre execution
  cases compiler <;> exact observed.2.2.1

-- These are results of universal decoded execution, including RET; the
-- independent literal counts cannot be justified by graph size alone.
example (compiler : EDSL.Corpus.V1.UnaryCode.Compiler)
    (operation : EDSL.Corpus.V1.UnaryCode.Operation)
    {input : EDSL.PureCall.Invocation (EDSL.Corpus.V1.UnaryCode.spec operation)}
    {initial : EDSL.X86.State}
    (pre : EDSL.PureCall.Pre (EDSL.Corpus.V1.UnaryCode.spec operation)
      (EDSL.Corpus.V1.UnaryCode.bytes compiler operation) input initial)
    {choices : EDSL.X86.Sequential.Choices} {result : EDSL.X86.Sequential.Result}
    (execution : EDSL.X86.Sequential.Executes choices initial result) :
    result.instructions = (match compiler, operation with
      | .defaultGCC, .absSigned32 => 5
      | .defaultClang, .absSigned32 => 4
      | .defaultGCC, .byteSwap64 => 4
      | .defaultClang, .byteSwap64 => 3) := by
  have observed := EDSL.Corpus.V1.UnaryBodies.observations compiler operation pre execution
  cases compiler <;> cases operation <;> exact observed.2.1

-- The concurrent provider selects exactly the registered row, and its full
-- files are the same immutable literals compared by the runtime CLI.
example (compiler : EDSL.Corpus.V1.FetchAddWindows.Compiler) :
    (EDSL.Corpus.V1.FetchAddCertificates.certificate compiler).input =
      EDSL.Corpus.V1.FetchAddWindows.input compiler := rfl
example (compiler : EDSL.Corpus.V1.FetchAddWindows.Compiler) :
    EDSL.Corpus.V1.FetchAddWindows.file compiler =
      EDSL.Corpus.V1.Comparisons.file compiler := rfl

#print axioms EDSL.Corpus.Reporting.acceptedCertificates
#print axioms EDSL.Corpus.Reporting.acceptedConcurrentCertificates
#print axioms EDSL.Corpus.Reporting.acceptedBufferCertificates
#print axioms EDSL.Corpus.Reporting.acceptedIndexSearchCertificates
#print axioms EDSL.Corpus.Reporting.acceptedByteComparisonCertificates
#print axioms EDSL.Corpus.Reporting.acceptedUnaryCertificates
#print axioms EDSL.Corpus.Reporting.acceptedPopcountCertificates
#print axioms EDSL.Corpus.Reporting.acceptedAverageCertificates
#print axioms EDSL.Corpus.Reporting.acceptedParityCertificates
#print axioms EDSL.Corpus.Reporting.acceptedRotationCertificates
#audit_edsl
LEAN

# Independently count the actual defined global c_* function names in each
# frozen ELF. Compare that inventory with the frozen extraction manifests in
# check-report.jq; neither native parsing nor a manifest supplies proof evidence.
corpus_function_symbols() {
    awk '$4 == "FUNC" && $5 == "GLOBAL" && $6 == "DEFAULT" &&
        $7 ~ /^[0-9]+$/ && $8 ~ /^c_[A-Za-z0-9_]+$/ {print $8}' "$1" | sort -u
}
record gcc-symbol-table readelf -sW "$gcc_file"
record clang-symbol-table readelf -sW "$clang_file"
record gcc-function-symbols corpus_function_symbols "$output/commands/gcc-symbol-table.stdout"
record clang-function-symbols corpus_function_symbols "$output/commands/clang-symbol-table.stdout"

# Frozen metadata and the independent native inventory constrain the report;
# formal file/name/semantics binding comes from the accepted typed families.
# The concurrent and read-only buffer operations require their fixed models;
# scalar rows retain their schema and cannot acquire a concurrent model tag.
cat > "$output/check-report.jq" <<'JQ'
def text: type == "string" and length > 0;
def natural: type == "number" and . >= 0 and floor == .;
def function_symbols: [.functions[].symbol] | unique;
def actual_symbols: split("\n") | map(select(length > 0));
def frozen_manifest($actual):
  type == "object" and
  (.functions | type == "array" and length == 40 and
    all(.[]; type == "object" and (.symbol | text))) and
  ($actual | length == 40 and (unique | length == 40)) and
  (function_symbols == $actual);
def certificate($manifest; $operation; $symbol; $proof):
  . as $c |
  type == "object" and .operation == $operation and .symbol == $symbol and .proof == $proof and
  (if $operation == "full64_fetch_add_concurrent" then
    .model == "managed-tso64-closed-batch-v1" and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "34" and .contract_id == "v1:34:c_atomic_fetch_add64")
   elif $operation == "first_bounded_nul_length" then
    .model == "sequential-read-only-x86-buffer-callable-v1" and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "18" and .contract_id == "v1:18:c_strnlen_bytes")
   elif $operation == "first_matching_byte_index" then
    .model == "sequential-read-only-x86-buffer-callable-v1" and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "21" and .contract_id == "v1:21:c_memchr_index")
   elif $operation == "first_matching_u32_index" then
    .model == "sequential-read-only-x86-buffer-callable-v1" and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "25" and .contract_id == "v1:25:c_linear_search_u32")
   elif $operation == "unsigned_lexicographic_bytes" then
    .model == "sequential-read-only-x86-buffer-callable-v1" and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "19" and .contract_id == "v1:19:c_memcmp_bytes")
   elif $operation == "signed_absolute32" then
    (has("model") | not) and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "04" and .contract_id == "v1:04:c_abs_i32")
   elif $operation == "byte_reverse64" then
    (has("model") | not) and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "10" and .contract_id == "v1:10:c_byteswap64")
   elif $operation == "population_count64" then
    (has("model") | not) and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "11" and .contract_id == "v1:11:c_popcount_loop")
   elif $operation == "unsigned_floor_average64" then
    (has("model") | not) and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "08" and .contract_id == "v1:08:c_average_u64")
   elif $operation == "parity64" then
    (has("model") | not) and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "12" and .contract_id == "v1:12:c_parity_loop")
   elif $operation == "rotate_left64" then
    (has("model") | not) and
    ([$manifest.functions[] | select(.symbol == $symbol)][0] |
      .definition_id == "09" and .contract_id == "v1:09:c_rotl64")
   else (has("model") | not) end) and
  (.file_offset | natural) and (.address | natural) and (.size | natural and . > 0) and
  ([$manifest.functions[] | select(.symbol == $symbol)] | length == 1) and
  ([$manifest.functions[] | select(.symbol == $symbol)][0] |
    .file_offset == $c.file_offset and .address == $c.address and .size == $c.size);
def search_extent($compiler; $operation):
  [.file_offset, .address, .size] ==
    (if $compiler == "gcc" and $operation == "byte" then [12288, 4206592, 40]
     elif $compiler == "gcc" and $operation == "u32" then [12512, 4206816, 40]
     elif $compiler == "clang" and $operation == "byte" then [5456, 4199760, 34]
     elif $compiler == "clang" and $operation == "u32" then [6128, 4200432, 34]
     else [] end);
def byte_comparison_extent($compiler):
  [.file_offset, .address, .size] ==
    (if $compiler == "gcc" then [12176, 4206480, 51]
     elif $compiler == "clang" then [5328, 4199632, 45]
     else [] end);
def unary_extent($compiler; $operation):
  [.file_offset, .address, .size] ==
    (if $compiler == "gcc" and $operation == "abs" then [11632, 4205936, 12]
     elif $compiler == "clang" and $operation == "abs" then [4864, 4199168, 8]
     elif $compiler == "gcc" and $operation == "swap" then [11760, 4206064, 11]
     elif $compiler == "clang" and $operation == "swap" then [4960, 4199264, 7]
     else [] end);
def artifact($compiler; $path; $bytes; $manifest; $enum):
  type == "object" and .compiler == $compiler and .path == $path and
  .bytes == $bytes and $manifest.elf_size == $bytes and
  .match == "complete_byte_equality" and
  (.certificates | type == "array" and length == 15) and
  (.certificates[0] | certificate($manifest; "unsigned_minimum64"; "c_min_u64";
    "EDSL.Corpus.V1.Comparisons.certificate " + $enum + " minimum")) and
  (.certificates[1] | certificate($manifest; "unsigned_maximum64"; "c_max_u64";
    "EDSL.Corpus.V1.Comparisons.certificate " + $enum + " maximum")) and
  (.certificates[2] | certificate($manifest; "unsigned_addition_modulo64"; "c_add_mod64";
    "EDSL.Corpus.V1.Arithmetic.certificate " + $enum)) and
  (.certificates[3] | certificate($manifest; "signed_clamp32"; "c_clamp_i32";
    "EDSL.Corpus.V1.Clamps.certificate " + $enum)) and
  (.certificates[4] | certificate($manifest; "full64_fetch_add_concurrent";
    "c_atomic_fetch_add64"; "EDSL.Corpus.V1.FetchAddCertificates.certificate " + $enum)) and
  (.certificates[5] | certificate($manifest; "first_bounded_nul_length";
    "c_strnlen_bytes"; "EDSL.Corpus.V1.ByteScanCertificates.certificate " + $enum)) and
  (.certificates[6] | certificate($manifest; "first_matching_byte_index";
    "c_memchr_index"; "EDSL.Corpus.V1.IndexSearchCertificates.certificate " + $enum + " byte")) and
  (.certificates[7] | certificate($manifest; "first_matching_u32_index";
    "c_linear_search_u32"; "EDSL.Corpus.V1.IndexSearchCertificates.certificate " + $enum + " u32")) and
  (.certificates[8] | certificate($manifest; "unsigned_lexicographic_bytes";
    "c_memcmp_bytes"; "EDSL.Corpus.V1.ByteComparisonCertificates.certificate " + $enum)) and
  (.certificates[9] | certificate($manifest; "signed_absolute32";
    "c_abs_i32"; "EDSL.Corpus.V1.UnaryCertificates.certificate " + $enum + " absSigned32")) and
  (.certificates[10] | certificate($manifest; "byte_reverse64";
    "c_byteswap64"; "EDSL.Corpus.V1.UnaryCertificates.certificate " + $enum + " byteSwap64")) and
  (.certificates[11] | certificate($manifest; "population_count64";
    "c_popcount_loop"; "EDSL.Corpus.V1.PopcountCertificates.certificate " + $enum)) and
  (.certificates[12] | certificate($manifest; "unsigned_floor_average64";
    "c_average_u64"; "EDSL.Corpus.V1.AverageCertificates.certificate " + $enum)) and
  (.certificates[13] | certificate($manifest; "parity64";
    "c_parity_loop"; "EDSL.Corpus.V1.ParityCertificates.certificate " + $enum)) and
  (.certificates[14] | certificate($manifest; "rotate_left64";
    "c_rotl64"; "EDSL.Corpus.V1.RotationCertificates.certificate " + $enum)) and
  (.certificates[6] | search_extent($compiler; "byte")) and
  (.certificates[7] | search_extent($compiler; "u32")) and
  (.certificates[8] | byte_comparison_extent($compiler)) and
  (.certificates[9] | unary_extent($compiler; "abs")) and
  (.certificates[10] | unary_extent($compiler; "swap")) and
  (.certificates[11] | [.file_offset, .address, .size] ==
    (if $compiler == "gcc" then [11776, 4206080, 31]
     elif $compiler == "clang" then [4976, 4199280, 28] else [] end)) and
  (.certificates[12] | [.file_offset, .address, .size] ==
    (if $compiler == "gcc" then [11712, 4206016, 20]
     elif $compiler == "clang" then [4928, 4199232, 16] else [] end)) and
  (.certificates[13] | [.file_offset, .address, .size] ==
    (if $compiler == "gcc" then [11808, 4206112, 33]
     elif $compiler == "clang" then [5008, 4199312, 36] else [] end)) and
  (.certificates[14] | [.file_offset, .address, .size] ==
    (if $compiler == "gcc" then [11744, 4206048, 13]
     elif $compiler == "clang" then [4944, 4199248, 9] else [] end)) and
  all(.certificates[]; .file_offset + .size <= $bytes) and
  ([.certificates[].symbol] | unique | length == 15) and
  ([.certificates[].operation] | unique | length == 15) and
  ([.certificates[] | [.file_offset, .address, .size]] | unique | length == 15) and
  (.certificates as $certificates | all($certificates[]; . as $a |
    all($certificates[]; . as $b | $a.symbol == $b.symbol or
      (($a.file_offset + $a.size <= $b.file_offset or
        $b.file_offset + $b.size <= $a.file_offset) and
       ($a.address + $a.size <= $b.address or $b.address + $b.size <= $a.address)))));
($gccSymbols | actual_symbols) as $gccNames |
($clangSymbols | actual_symbols) as $clangNames |
($gccManifest | length == 1) and ($clangManifest | length == 1) and
($gccManifest[0] | frozen_manifest($gccNames)) and
($clangManifest[0] | frozen_manifest($clangNames)) and
($gccNames == $clangNames) and
length == 1 and (.[0] |
  type == "object" and .schema == "edsl.compiler-corpus.certificates.v1" and
  .status == "certified_under_recorded_model_assumptions" and
  .score == {functions_certified_end_to_end: 15,
    functions_total: ($gccNames | length),
    compiler_artifacts_certified_end_to_end: 30,
    compiler_artifacts_total: (($gccNames | length) + ($clangNames | length)),
    concurrency_contracts_proved: 1} and
  (.files | type == "array" and length == 2) and
  (.files[0] | artifact("gcc"; $gcc; $gccBytes; $gccManifest[0]; "defaultGCC")) and
  (.files[1] | artifact("clang"; $clang; $clangBytes; $clangManifest[0]; "defaultClang")) and
  ([.files[] | .compiler as $compiler | .certificates[] |
      [$compiler, .operation, .symbol]] | unique | length == 30) and
  ([.files[].certificates[].proof] | unique | length == 30) and
  ([.files[].certificates[].symbol] | unique | length == 15) and
  ([.files[].certificates[].operation] | unique | length == 15) and
  ([.files[].certificates[] | select(.operation == "full64_fetch_add_concurrent")] |
    length == 2 and (map(.symbol) | unique | length == 1)) and
  (.score.functions_certified_end_to_end ==
    ([.files[].certificates[].symbol] | unique | length)) and
  (.score.compiler_artifacts_certified_end_to_end == ([.files[].certificates[]] | length)) and
  (.score.concurrency_contracts_proved ==
    ([.files[].certificates[] | select(.operation == "full64_fetch_add_concurrent") |
      [.operation, .symbol, .model]] | unique | length)) and
  .profile.long_mode == true and .profile.cet_ibt_enabled == false and
  .profile.shadow_stack_enabled == false and .profile.multi_byte_nop == true and
  .profile.status == "recorded model assumptions; native configuration is not checked" and
  (.stages | type == "object" and
    all(.complete_file_identity, .elf_symbol_binding, .cfg, .symbolic_vc,
      .registered_semantics, .unary_semantics, .unary_progress, .population_count_semantics,
      .average_semantics, .average_progress, .parity_semantics,
      .rotation_semantics, .rotation_progress,
      .buffer_semantics, .index_search_semantics,
      .byte_comparison_semantics, .byte_comparison_resources, .byte_comparison_progress,
      .concurrent_semantics, .concurrent_progress,
      .concurrent_resources, .concurrent_useful_domain,
      .caller_resources, .useful_domain, .certificate_axioms; text)) and
  ([.stages.complete_file_identity, .stages.elf_symbol_binding, .stages.cfg,
    .stages.symbolic_vc, .stages.registered_semantics, .stages.caller_resources,
    .stages.useful_domain, .stages.certificate_axioms, .stages.concurrent_semantics,
    .stages.concurrent_progress, .stages.concurrent_resources,
    .stages.concurrent_useful_domain, .stages.buffer_semantics,
    .stages.index_search_semantics, .stages.unary_semantics, .stages.unary_progress,
    .stages.population_count_semantics, .stages.average_semantics, .stages.average_progress,
    .stages.parity_semantics, .stages.rotation_semantics, .stages.rotation_progress,
    .stages.byte_comparison_semantics,
    .stages.byte_comparison_resources, .stages.byte_comparison_progress] |
      unique | length == 25) and
  (.stages.population_count_semantics | contains("full64 input bit-position cardinality") and
    contains("unsigned low32") and contains("all inputs including zero and all-ones admitted") and
    contains("every AF stream terminates") and contains("strict remaining-cardinality rank") and
    contains("complete RAM and original caller resources") and
    contains("every prefix and return") and contains("ABI and result established at return")) and
  (.stages.parity_semantics | contains("independent full64 input bit-position cardinality modulo 2") and
    contains("returned as unsigned low32") and
    contains("all full64 words including zero and all-ones admitted") and
    contains("upper32 RAX unconstrained") and
    contains("useful endpoint witness 0x8000000000000001 does not restrict the domain") and
    contains("every AF stream terminates by strict unsigned remainder rank") and
    contains("complete RAM and permissions, original caller and current code authority") and
    contains("retained at every prefix and return") and
    contains("ABI and result established at return") and
    contains("no physical/OS/compiler refinement or minimum-cost claim")) and
  (.stages.average_semantics | contains("full64 RDI/RSI inputs") and
    contains("unsigned floor of the unbounded natural input sum divided by two") and
    contains("all full64 pairs including overflowing input sums admitted") and
    contains("every AF stream terminates") and
    contains("complete RAM and original caller resources") and
    contains("every prefix and return") and contains("ABI and result established at return")) and
  (.stages.average_progress | contains("average GCC 7, Clang 6") and
    contains("including RET and GCC ENDBR64") and
    contains("universal decoded-execution observations") and
    contains("no physical timing or minimum-cost claim")) and
  (.stages.rotation_semantics | contains("independent full64 bit-origin left rotation") and
    contains("unsigned low32 RSI modulo 64") and
    contains("all full64 RDI values and all low32 counts admitted") and
    contains("arbitrary upper32 RSI") and
    contains("every independent undefined-flag choice stream terminates") and
    contains("zero count retains all flags, one count defines OF, larger counts permit either OF") and
    contains("complete RAM and permissions, original caller and current code authority") and
    contains("retained at every prefix and return") and contains("ABI and result established at return")) and
  (.stages.rotation_progress | contains("rotation GCC 5, Clang 4") and
    contains("including RET and GCC ENDBR64") and
    contains("universal decoded-execution observations") and
    contains("no physical timing or minimum-cost claim")) and
  (.stages.unary_semantics | contains("nonnegative") and contains("mathematical square") and
    contains("excludes INT32_MIN") and contains("arbitrary argument upper halves") and
    contains("all eight base-256 digits") and contains("every admitted resource call") and
    contains("every AF stream")) and
  (.stages.unary_progress | contains("absolute value GCC 5, Clang 4") and
    contains("byte reversal GCC 4, Clang 3") and contains("including RET and GCC ENDBR64") and
    contains("no physical timing or minimum-cost claim")) and
  (.stages.buffer_semantics | contains("n < 2^64") and
    contains("dynamic rank") and contains("n=0 requires no data loan")) and
  (.stages.index_search_semantics | contains("earliest matching") and
    contains("little-endian u32") and contains("full64 SIZE_MAX when absent") and
    contains("n < 2^64") and contains("low8/low32") and
    contains("arbitrary upper bits") and contains("all AF streams") and
    contains("dynamic rank") and contains("original caller, full RAM, ABI") and
    contains("every-prefix current read authority") and
    contains("n=0 requires no data loan or pointer validity")) and
  (.stages.byte_comparison_semantics | contains("signed low32 C-int return sign") and
    contains("independent unsigned-byte List.Lex") and
    contains("arbitrary equal-length complete snapshots") and contains("n < 2^64") and
    contains("full64 RDI/RSI/RDX") and contains("both pointers and count") and
    contains("DATA1 reads stay within the two exact input spans") and
    contains("compatible overlapping, identical, unaligned, code and caller aliases") and
    contains("n=0 ignores both pointers and input-loan selectors") and
    contains("no DATA loan") and contains("no DATA read")) and
  (.stages.byte_comparison_resources | contains("complete RAM and permissions") and
    contains("current code, original caller and both nonempty input loans") and
    contains("every prefix and return") and contains("ABI frames and nonarithmetic flags")) and
  (.stages.byte_comparison_progress | contains("all AF streams") and
    contains("terminate by dynamic rank") and
    contains("9*(n+2) is a proved output upper bound on retired model instructions") and
    contains("no physical cost or minimum-cost claim")) and
  (.stages.registered_semantics | contains("signed low32") and
    contains("lower <= upper") and contains("arbitrary argument upper halves")) and
  (.stages.concurrent_semantics | contains("CLOSED-COHORT") and
    contains("current-only ABI admission") and contains("arbitrary full64 initial values and deltas") and
    contains("every successful finite returned schedule") and
    contains("independent legal modulo-counter histories") and
    contains("exact selected RMW/call occurrence coverage")) and
  (.stages.concurrent_progress | contains("every successful finite prefix") and
    contains("safety and current authority") and contains("enabled actual issue") and
    contains("every AF value") and contains("global completion") and
    contains("own-issue bound is proved as output")) and
  (.stages.concurrent_resources | contains("return continuation") and
    contains("callee-save") and contains("stack, DF and collect") and
    contains("resources and byte frames") and contains("full installed ELF") and
    contains("current authority")) and
  (.stages.concurrent_useful_domain | contains("actual loaded overlapping completed execution") and
    contains("useful nonzero-delta") and contains("both RMWs before the first call returns")) and
  .stages.native_execution == "not used as proof evidence" and
  (.limits | type == "array" and all(.[]; text) and
    any(.[]; contains("Stable modeled RAM") and contains("executable text") and contains("resource")) and
    any(.[]; contains("modeled ownership") and contains("does not authenticate")) and
    any(.[]; contains("No source/IR preservation") and contains("physical CPU") and
      contains("CET-enabled") and contains("native Linux startup")) and
    any(.[]; contains("relocation") and contains("asynchronous interference") and
      contains("outside the fixed managed closed cohort/profile")) and
    any(.[]; contains("Scalar certificates") and contains("exclude concurrent interference")) and
    any(.[]; contains("modeled managed profile") and contains("no published physical x86-TSO") and
      contains("Linux/GNU memory-order") and contains("scheduling fairness") and
      contains("hardware-minimum progress bound")) and
    any(.[]; contains("Byte comparison") and contains("current borrowed sequential callable profile") and
      contains("stable ordinary RAM") and contains("absent asynchronous interference") and
      contains("CET off") and contains("no source/LLVM preservation") and
      contains("native Linux") and contains("concurrent-buffer claim")) and
    all(.[]; contains("concurrent histories receive no certificate") | not) and
    any(.[]; contains("not future filesystem or process mappings")) and
    any(.[]; contains("Fresh kernel replay is a separate verification-gate step"))))
JQ
gate_inputs=("$output/Audit.lean" "$output/check-report.jq" "$output/scope.txt"
    "$output/fresh-target.txt" "$output/fresh-receipt-label.txt")
if [[ $full_project == true ]]; then
    gate_inputs+=("$output/source/CorpusFullReplay.lean")
fi
record gate-inputs sha256sum -- "${gate_inputs[@]}"
record save-gate-inputs cp -- "$output/commands/gate-inputs.stdout" "$output/gate-inputs.sha256"

certificate_targets=(EDSL.Corpus.V1.Comparisons EDSL.Corpus.V1.Arithmetic EDSL.Corpus.V1.Clamps
    EDSL.Corpus.V1.FetchAddCertificates EDSL.Corpus.V1.ByteScanCertificates
    EDSL.Corpus.V1.IndexSearchCertificates EDSL.Corpus.V1.ByteComparisonCertificates
    EDSL.Corpus.V1.UnaryCertificates EDSL.Corpus.V1.PopcountCertificates
    EDSL.Corpus.V1.AverageCertificates EDSL.Corpus.V1.ParityCertificates
    EDSL.Corpus.V1.RotationCertificates)
if [[ $full_project == true ]]; then
    record build-full-project "${lean_lock[@]}" lake build EDSL.All VerificationTests UnaryTests PopcountTests AverageTests ParityTests RotationTests Low8Tests ByteEqualityTests CFGProfileTests \
        edsl-proof-export edsl-grade "${certificate_targets[@]}"
else
    record build "${lean_lock[@]}" lake build "${certificate_targets[@]}"
fi
if [[ $full_project == true ]]; then
    record cli-binaries-before sha256sum -- \
        .lake/build/bin/edsl-proof-export .lake/build/bin/edsl-grade
    record save-cli-binary-hashes cp -- "$output/commands/cli-binaries-before.stdout" \
        "$output/cli-binaries-before.sha256"
fi
# Library owners may still be integrating. Reject a moved source snapshot now,
# before paying for a full fresh replay. EXIT also checks every final input.
record source-after-build bash -o pipefail -c "$source_hash_command"
record source-before-proof-stable cmp -- "$output/source-before.sha256" \
    "$output/commands/source-after-build.stdout"
record compile-cli "${lean_env[@]}" lean -DwarningAsError=true \
    -o "$output/lib/corpus/Certify.olean" corpus/Certify.lean
if [[ $full_project == true ]]; then
    record compile-project-corpus-aggregate "${lean_env[@]}" lean -DwarningAsError=true \
        --root="$output/source" -o "$output/lib/CorpusFullReplay.olean" \
        "$output/source/CorpusFullReplay.lean"
fi
record modules-before bash -o pipefail -c "$module_hash_command"
record save-module-hashes cp -- "$output/commands/modules-before.stdout" "$output/modules-before.sha256"
record axiom-audit "${lean_env[@]}" lean -DwarningAsError=true "$output/Audit.lean"

record gcc-size wc -c "$gcc_file"
record clang-size wc -c "$clang_file"
read -r gcc_size _ < "$output/commands/gcc-size.stdout"
read -r clang_size _ < "$output/commands/clang-size.stdout"

report_json_with_manifests() {
    local gcc_path=$1 clang_path=$2 file=$3 gcc_manifest=$4 clang_manifest=$5
    jq -e -s --arg gcc "$gcc_path" --arg clang "$clang_path" \
        --argjson gccBytes "$gcc_size" --argjson clangBytes "$clang_size" \
        --slurpfile gccManifest "$gcc_manifest" \
        --slurpfile clangManifest "$clang_manifest" \
        --rawfile gccSymbols "$output/commands/gcc-function-symbols.stdout" \
        --rawfile clangSymbols "$output/commands/clang-function-symbols.stdout" \
        -f "$output/check-report.jq" "$file"
}
report_json() {
    report_json_with_manifests "$1" "$2" "$3" \
        corpus/v1/gcc/manifest.json corpus/v1/clang/manifest.json
}
check_report() {
    local name=$1 gcc_path=$2 clang_path=$3 file=$4 lines
    record "$name-one-line" awk 'END {exit (NR != 1)}' "$file"
    record "$name-linefeeds" wc -l "$file"
    read -r lines _ < "$output/commands/$name-linefeeds.stdout"
    record "$name-newline" test "$lines" -eq 1
    record "$name-json" report_json "$gcc_path" "$clang_path" "$file"
    record "$name-stderr-empty" test ! -s "$output/commands/$name.stderr"
}

record cli-default "${cli[@]}"
check_report cli-default "$gcc_file" "$clang_file" "$output/commands/cli-default.stdout"
record save-report cp -- "$output/commands/cli-default.stdout" "$output/report.json"
record cli-repeat "${cli[@]}"
check_report cli-repeat "$gcc_file" "$clang_file" "$output/commands/cli-repeat.stdout"
record deterministic-report cmp -- "$output/report.json" "$output/commands/cli-repeat.stdout"

valid_gcc=$output/mutations/valid-gcc.elf
valid_clang=$output/mutations/valid-clang.elf
record copy-valid-gcc cp -- "$gcc_file" "$valid_gcc"
record copy-valid-clang cp -- "$clang_file" "$valid_clang"
record valid-gcc-identical cmp -- "$gcc_file" "$valid_gcc"
record valid-clang-identical cmp -- "$clang_file" "$valid_clang"
record cli-gcc-flag "${cli[@]}" --gcc "$valid_gcc"
check_report cli-gcc-flag "$valid_gcc" "$clang_file" "$output/commands/cli-gcc-flag.stdout"
record cli-clang-flag "${cli[@]}" --clang "$valid_clang"
check_report cli-clang-flag "$gcc_file" "$valid_clang" "$output/commands/cli-clang-flag.stdout"
record cli-both-flags "${cli[@]}" --gcc "$valid_gcc" --clang "$valid_clang"
check_report cli-both-flags "$valid_gcc" "$valid_clang" "$output/commands/cli-both-flags.stdout"
record cli-reversed-flags "${cli[@]}" --clang "$valid_clang" --gcc "$valid_gcc"
check_report cli-reversed-flags "$valid_gcc" "$valid_clang" "$output/commands/cli-reversed-flags.stdout"
record flag-order-determinism cmp -- "$output/commands/cli-both-flags.stdout" \
    "$output/commands/cli-reversed-flags.stdout"

expect_status() {
    local expected=$1 name=$2 observed=0
    shift 2
    printf '%s\n' "$expected" > "$output/commands/$name.expected-exit"
    record "$name" "$@" || observed=$?
    if [[ $observed -ne $expected ]]; then
        printf 'Expected %s from %s; observed %s\n' "$expected" "$name" "$observed" >&2
        return 1
    fi
}
reject() {
    local expected=$1 name=$2
    shift 2
    expect_status "$expected" "$name" "${cli[@]}" "$@"
    record "$name-stdout-empty" test ! -s "$output/commands/$name.stdout"
    record "$name-stderr-present" test -s "$output/commands/$name.stderr"
}

# These controls exercise the report validator, not the Lean proof. Mutate the
# real accepted report while keeping the frozen inputs and typed anchors fixed.
# Check each compiler independently: a valid GCC row cannot hide a bad Clang row.
reject_report() {
    local name=$1 filter=$2
    shift 2
    record "$name-mutate" jq "$@" "$filter" "$output/report.json"
    record "$name-save" cp -- "$output/commands/$name-mutate.stdout" \
        "$output/mutations/$name.json"
    expect_status 1 "$name" report_json "$gcc_file" "$clang_file" \
        "$output/mutations/$name.json"
    record "$name-stderr-empty" test ! -s "$output/commands/$name.stderr"
}
reject_report reject-report-schema '.schema = "edsl.compiler-corpus.certificates.v2"'
reject_report reject-report-function-count '.score.functions_certified_end_to_end = 6'
reject_report reject-report-artifact-count '.score.compiler_artifacts_certified_end_to_end = 12'
reject_report reject-report-historical-function-count '.score.functions_certified_end_to_end = 8'
reject_report reject-report-historical-artifact-count '.score.compiler_artifacts_certified_end_to_end = 16'
reject_report reject-report-pre-unary-function-count '.score.functions_certified_end_to_end = 9'
reject_report reject-report-pre-unary-artifact-count '.score.compiler_artifacts_certified_end_to_end = 18'
reject_report reject-report-pre-popcount-function-count '.score.functions_certified_end_to_end = 11'
reject_report reject-report-pre-popcount-artifact-count '.score.compiler_artifacts_certified_end_to_end = 22'
reject_report reject-report-pre-average-function-count '.score.functions_certified_end_to_end = 12'
reject_report reject-report-pre-average-artifact-count '.score.compiler_artifacts_certified_end_to_end = 24'
reject_report reject-report-pre-parity-function-count '.score.functions_certified_end_to_end = 13'
reject_report reject-report-pre-parity-artifact-count '.score.compiler_artifacts_certified_end_to_end = 26'
reject_report reject-report-pre-rotation-function-count '.score.functions_certified_end_to_end = 14'
reject_report reject-report-pre-rotation-artifact-count '.score.compiler_artifacts_certified_end_to_end = 28'
reject_report reject-report-concurrency-count '.score.concurrency_contracts_proved = 2'
report_compilers=(gcc clang)
for index in 0 1; do
    label=${report_compilers[$index]}
    # Keep jq variables literal; their values enter through --argjson only.
    while IFS=$'\t' read -r mutation filter; do
        reject_report "reject-$label-concurrent-$mutation" "$filter" --argjson index "$index"
    done <<'MUTATIONS'
missing-model	del(.files[$index].certificates[4].model)
model	.files[$index].certificates[4].model = "physical-x86-tso"
operation	.files[$index].certificates[4].operation = "unsigned_addition_modulo64"
proof	.files[$index].certificates[4].proof = .files[1 - $index].certificates[4].proof
symbol	.files[$index].certificates[4].symbol = "c_atomic_load_acquire64"
offset	.files[$index].certificates[4].file_offset += 1
address	.files[$index].certificates[4].address += 1
size	.files[$index].certificates[4].size -= 1
duplicate	.files[$index].certificates[3] = .files[$index].certificates[4]
missing-row	del(.files[$index].certificates[4])
MUTATIONS
    while IFS=$'\t' read -r mutation filter; do
        reject_report "reject-$label-buffer-$mutation" "$filter" --argjson index "$index"
    done <<'MUTATIONS'
missing-model	del(.files[$index].certificates[5].model)
model	.files[$index].certificates[5].model = "physical-linux-callable"
operation	.files[$index].certificates[5].operation = "unsigned_minimum64"
proof	.files[$index].certificates[5].proof = .files[1 - $index].certificates[5].proof
symbol	.files[$index].certificates[5].symbol = "c_memchr_index"
offset	.files[$index].certificates[5].file_offset += 1
address	.files[$index].certificates[5].address += 1
size	.files[$index].certificates[5].size -= 1
duplicate	.files[$index].certificates[3] = .files[$index].certificates[5]
missing-row	del(.files[$index].certificates[5])
MUTATIONS
    for entry in 6 7; do
        width=byte
        [[ $entry -eq 6 ]] || width=u32
        while IFS=$'\t' read -r mutation filter; do
            reject_report "reject-$label-search-$width-$mutation" "$filter" \
                --argjson index "$index" --argjson entry "$entry"
        done <<'MUTATIONS'
missing-model	del(.files[$index].certificates[$entry].model)
model	.files[$index].certificates[$entry].model = "physical-linux-callable"
operation	.files[$index].certificates[$entry].operation = "first_bounded_nul_length"
compiler-proof	.files[$index].certificates[$entry].proof = .files[1 - $index].certificates[$entry].proof
width-proof	.files[$index].certificates[$entry].proof = .files[$index].certificates[13 - $entry].proof
symbol	.files[$index].certificates[$entry].symbol = "c_strnlen_bytes"
offset	.files[$index].certificates[$entry].file_offset += 1
address	.files[$index].certificates[$entry].address += 1
size	.files[$index].certificates[$entry].size -= 1
duplicate	.files[$index].certificates[3] = .files[$index].certificates[$entry]
missing-row	del(.files[$index].certificates[$entry])
doubled-row	.files[$index].certificates += [.files[$index].certificates[$entry]]
MUTATIONS
    done
    read -r filter <<'JQ'
.files[$index].certificates |= .[0:6] + [.[7], .[6]] + .[8:]
JQ
    reject_report "reject-$label-search-width-swap" "$filter" --argjson index "$index"
    while IFS=$'\t' read -r mutation filter; do
        reject_report "reject-$label-byte-comparison-$mutation" "$filter" \
            --argjson index "$index"
    done <<'MUTATIONS'
missing-model	del(.files[$index].certificates[8].model)
model	.files[$index].certificates[8].model = "physical-linux-callable"
operation	.files[$index].certificates[8].operation = "first_bounded_nul_length"
compiler-proof	.files[$index].certificates[8].proof = .files[1 - $index].certificates[8].proof
task-proof	.files[$index].certificates[8].proof = .files[$index].certificates[5].proof
symbol	.files[$index].certificates[8].symbol = "c_strnlen_bytes"
offset	.files[$index].certificates[8].file_offset += 1
address	.files[$index].certificates[8].address += 1
size	.files[$index].certificates[8].size -= 1
duplicate	.files[$index].certificates[3] = .files[$index].certificates[8]
missing-row	del(.files[$index].certificates[8])
doubled-row	.files[$index].certificates += [.files[$index].certificates[8]]
row-swap	.files[$index].certificates |= .[0:7] + [.[8], .[7]] + .[9:]
MUTATIONS
    for entry in 9 10 11 12 13 14; do
        case "$entry" in
            9) operation=absolute ;;
            10) operation=byte-reverse ;;
            11) operation=popcount ;;
            12) operation=average ;;
            13) operation=parity ;;
            14) operation=rotation ;;
        esac
        while IFS=$'\t' read -r mutation filter; do
            reject_report "reject-$label-scalar-$operation-$mutation" "$filter" \
                --argjson index "$index" --argjson entry "$entry"
        done <<'MUTATIONS'
model	.files[$index].certificates[$entry].model = "physical-linux-callable"
operation	.files[$index].certificates[$entry].operation = "unsigned_minimum64"
compiler-proof	.files[$index].certificates[$entry].proof = .files[1 - $index].certificates[$entry].proof
task-proof	.files[$index].certificates[$entry].proof = .files[$index].certificates[(if $entry == 12 then 2 else 19 - $entry end)].proof
symbol	.files[$index].certificates[$entry].symbol = "c_clamp_i32"
offset	.files[$index].certificates[$entry].file_offset += 1
address	.files[$index].certificates[$entry].address += 1
size	.files[$index].certificates[$entry].size -= 1
missing-row	del(.files[$index].certificates[$entry])
doubled-row	.files[$index].certificates += [.files[$index].certificates[$entry]]
MUTATIONS
    done
    # Same input/output shape, different mathematics: a population-count row
    # or proof cannot supply parity's registered bit-cardinality modulo two.
    while IFS=$'\t' read -r mutation filter; do
        reject_report "reject-$label-parity-$mutation" "$filter" --argjson index "$index"
    done <<'MUTATIONS'
popcount-operation	.files[$index].certificates[13].operation = "population_count64"
popcount-proof	.files[$index].certificates[13].proof = .files[$index].certificates[11].proof
duplicate	.files[$index].certificates[12] = .files[$index].certificates[13]
MUTATIONS
done
reject_report reject-unary-stage-missing 'del(.stages.unary_semantics)'
reject_report reject-unary-domain-weakened \
    '.stages.unary_semantics |= sub("excludes INT32_MIN"; "includes every signed input")'
reject_report reject-unary-upper-halves \
    '.stages.unary_semantics |= sub("arbitrary argument upper halves"; "zero argument upper halves")'
reject_report reject-unary-progress-physical \
    '.stages.unary_progress = "physical minimum cost GCC 5 Clang 4"'
reject_report reject-popcount-stage-missing 'del(.stages.population_count_semantics)'
reject_report reject-popcount-domain-restricted \
    '.stages.population_count_semantics |= sub("all inputs including zero and all-ones admitted"; "only positive counts admitted")'
reject_report reject-popcount-progress-unproved \
    '.stages.population_count_semantics |= sub("strict remaining-cardinality rank"; "loop assumed to terminate")'
reject_report reject-average-stage-missing 'del(.stages.average_semantics)'
reject_report reject-average-wrapped-sum \
    '.stages.average_semantics |= sub("unbounded natural input sum"; "input sum modulo 2^64")'
reject_report reject-average-domain-restricted \
    '.stages.average_semantics |= sub("all full64 pairs including overflowing input sums admitted"; "only nonoverflowing input sums admitted")'
reject_report reject-average-argument-width \
    '.stages.average_semantics |= sub("full64 RDI/RSI inputs"; "low32 RDI/RSI inputs")'
reject_report reject-average-af-streams \
    '.stages.average_semantics |= sub("every AF stream terminates"; "one AF stream terminates")'
reject_report reject-average-prefix-resources \
    '.stages.average_semantics |= sub("every prefix and return"; "return only")'
reject_report reject-average-abi-scope \
    '.stages.average_semantics |= sub("ABI and result established at return"; "ABI and result assumed in admission")'
reject_report reject-average-progress-missing 'del(.stages.average_progress)'
reject_report reject-average-progress-count \
    '.stages.average_progress |= sub("average GCC 7, Clang 6"; "average GCC 6, Clang 5")'
reject_report reject-average-progress-physical \
    '.stages.average_progress = "average GCC 7, Clang 6 physical minimum operations"'
while IFS=$'\t' read -r mutation filter; do
    reject_report "reject-rotation-$mutation" "$filter"
done <<'MUTATIONS'
stage-missing	del(.stages.rotation_semantics)
direction	.stages.rotation_semantics |= sub("bit-origin left rotation"; "bit-origin right rotation")
count-width	.stages.rotation_semantics |= sub("unsigned low32 RSI modulo 64"; "full64 RSI modulo 64")
argument-width	.stages.rotation_semantics |= sub("full64 RDI values"; "low32 RDI values")
domain	.stages.rotation_semantics |= sub("all low32 counts admitted"; "only counts below 64 admitted")
upper-rsi	.stages.rotation_semantics |= sub("arbitrary upper32 RSI"; "zero upper32 RSI")
choice-streams	.stages.rotation_semantics |= sub("every independent undefined-flag choice stream terminates"; "one undefined-flag choice stream terminates")
zero-flags	.stages.rotation_semantics |= sub("zero count retains all flags"; "zero count clears flags")
of-choice	.stages.rotation_semantics |= sub("larger counts permit either OF"; "larger counts force OF=false")
caller-resources	.stages.rotation_semantics |= sub("original caller and current code authority"; "replacement caller and formerly loaded code")
prefix	.stages.rotation_semantics |= sub("every prefix and return"; "return only")
abi	.stages.rotation_semantics |= sub("ABI and result established at return"; "ABI and result assumed in admission")
progress-missing	del(.stages.rotation_progress)
retired	.stages.rotation_progress |= sub("rotation GCC 5, Clang 4"; "rotation GCC 4, Clang 3")
physical	.stages.rotation_progress = "rotation GCC 5, Clang 4 physical minimum operations"
MUTATIONS
while IFS=$'\t' read -r mutation filter; do
    reject_report "reject-parity-$mutation" "$filter"
done <<'MUTATIONS'
stage-missing	del(.stages.parity_semantics)
argument-high64	.stages.parity_semantics |= sub("full64 input bit-position cardinality"; "low32 input bit-position cardinality")
domain-restricted	.stages.parity_semantics |= sub("all full64 words including zero and all-ones admitted"; "only nonzero words with at most 63 set bits admitted")
low32-result	.stages.parity_semantics |= sub("returned as unsigned low32"; "returned as signed full64")
upper-rax	.stages.parity_semantics |= sub("upper32 RAX unconstrained"; "upper32 RAX must be zero")
popcount-result	.stages.parity_semantics |= sub("cardinality modulo 2"; "cardinality")
useful-domain	.stages.parity_semantics |= sub("does not restrict the domain"; "is the only admitted input")
af-streams	.stages.parity_semantics |= sub("every AF stream terminates"; "one AF stream terminates")
remainder-rank	.stages.parity_semantics |= sub("strict unsigned remainder rank"; "assumed loop termination")
ram-permissions	.stages.parity_semantics |= sub("complete RAM and permissions"; "selected stack bytes")
original-caller	.stages.parity_semantics |= sub("original caller"; "replacement caller")
code-authority	.stages.parity_semantics |= sub("current code authority"; "formerly loaded code")
prefix-resources	.stages.parity_semantics |= sub("retained at every prefix and return"; "retained at return only")
abi-scope	.stages.parity_semantics |= sub("ABI and result established at return"; "ABI and result assumed in admission")
physical-claim	.stages.parity_semantics |= sub("no physical/OS/compiler refinement or minimum-cost claim"; "physical CPU and OS refinement with compiler preservation and minimum cost")
MUTATIONS
read -r filter <<'JQ'
.files[0].certificates[6:8] as $gcc | .files[0].certificates[6:8] = .files[1].certificates[6:8] | .files[1].certificates[6:8] = $gcc
JQ
reject_report reject-search-compiler-swap "$filter"
reject_report reject-search-stage-missing 'del(.stages.index_search_semantics)'
reject_report reject-search-stage-weakened \
    '.stages.index_search_semantics = "finite observations on selected snapshots"'
read -r filter <<'JQ'
.files[0].certificates[8] as $gcc | .files[0].certificates[8] = .files[1].certificates[8] | .files[1].certificates[8] = $gcc
JQ
reject_report reject-byte-comparison-compiler-swap "$filter"
while IFS=$'\t' read -r mutation filter; do
    reject_report "reject-byte-comparison-$mutation" "$filter"
done <<'MUTATIONS'
stage-missing	del(.stages.byte_comparison_semantics)
return-width	.stages.byte_comparison_semantics |= sub("signed low32 C-int return sign"; "signed full64 return sign")
signed-bytes	.stages.byte_comparison_semantics |= sub("unsigned-byte List.Lex"; "signed-byte List.Lex")
bounded-snapshots	.stages.byte_comparison_semantics |= sub("arbitrary equal-length complete snapshots with n < 2\\^64"; "selected snapshots of at most 32 bytes")
argument-width	.stages.byte_comparison_semantics |= sub("full64 RDI/RSI/RDX"; "low32 RDI/RSI/RDX")
read-width	.stages.byte_comparison_semantics |= sub("DATA1"; "DATA8")
aliases	.stages.byte_comparison_semantics |= sub("compatible overlapping, identical, unaligned, code and caller aliases admitted"; "disjoint aligned inputs required")
empty-pointers	.stages.byte_comparison_semantics |= sub("n=0 ignores both pointers and input-loan selectors"; "n=0 requires valid pointers and live input-loan selectors")
empty-loans	.stages.byte_comparison_semantics |= sub("no DATA loan"; "two DATA loans")
empty-reads	.stages.byte_comparison_semantics |= sub("no DATA read"; "one DATA read")
resources-missing	del(.stages.byte_comparison_resources)
ram-permissions	.stages.byte_comparison_resources |= sub("complete RAM and permissions"; "selected input bytes")
caller-loans	.stages.byte_comparison_resources |= sub("original caller and both nonempty input loans"; "replacement caller and one input loan")
prefix-resources	.stages.byte_comparison_resources |= sub("every prefix and return"; "return only")
abi-flags	.stages.byte_comparison_resources |= sub("ABI frames and nonarithmetic flags"; "RAX only")
current-code	.stages.byte_comparison_resources |= sub("current code"; "formerly loaded code")
progress-missing	del(.stages.byte_comparison_progress)
af-streams	.stages.byte_comparison_progress |= sub("all AF streams"; "one AF stream")
physical-bound	.stages.byte_comparison_progress = "all AF streams terminate by dynamic rank; 9*(n+2) is a physical minimum cost"
limits	del(.limits[] | select(contains("Byte comparison")))
MUTATIONS

# Keep the report valid while mutating the selected frozen registration, so a
# validator that accepts the wrong independent task identity is also caught.
for label in gcc clang; do
    for symbol in c_memchr_index c_linear_search_u32 c_memcmp_bytes c_abs_i32 c_byteswap64 c_average_u64 c_parity_loop c_rotl64; do
        while IFS=$'\t' read -r mutation filter; do
            name=reject-$label-$symbol-manifest-$mutation
            record "$name-mutate" jq --arg symbol "$symbol" "$filter" \
                "corpus/v1/$label/manifest.json"
            record "$name-save" cp -- "$output/commands/$name-mutate.stdout" \
                "$output/mutations/$name.json"
            gcc_manifest=corpus/v1/gcc/manifest.json
            clang_manifest=corpus/v1/clang/manifest.json
            if [[ $label == gcc ]]; then
                gcc_manifest=$output/mutations/$name.json
            else
                clang_manifest=$output/mutations/$name.json
            fi
            expect_status 1 "$name" report_json_with_manifests "$gcc_file" "$clang_file" \
                "$output/report.json" "$gcc_manifest" "$clang_manifest"
            record "$name-stderr-empty" test ! -s "$output/commands/$name.stderr"
        done <<'MUTATIONS'
definition-id	(.functions[] | select(.symbol == $symbol)).definition_id = "18"
contract-id	(.functions[] | select(.symbol == $symbol)).contract_id = "v1:18:c_strnlen_bytes"
MUTATIONS
    done
done

# Change an extent in both report and manifest. Agreement with
# supplied metadata must not replace the independently frozen complete extent.
read -r report_extent_mutation <<'JQ'
.files[$index].certificates[$entry][$field] += $delta
JQ
read -r manifest_extent_mutation <<'JQ'
(.functions[] | select(.symbol == $symbol))[$field] += $delta
JQ
for operation in byte-comparison average parity rotation; do
    case "$operation" in
        byte-comparison) entry=8 symbol=c_memcmp_bytes ;;
        average) entry=12 symbol=c_average_u64 ;;
        parity) entry=13 symbol=c_parity_loop ;;
        rotation) entry=14 symbol=c_rotl64 ;;
    esac
    for index in 0 1; do
        label=${report_compilers[$index]}
        while IFS=$'\t' read -r field delta; do
            name=reject-$label-$operation-joint-$field
            record "$name-report-mutate" jq --argjson index "$index" --argjson entry "$entry" \
                --arg field "$field" --argjson delta "$delta" "$report_extent_mutation" \
                "$output/report.json"
            record "$name-report-save" cp -- "$output/commands/$name-report-mutate.stdout" \
                "$output/mutations/$name-report.json"
            record "$name-manifest-mutate" jq --arg symbol "$symbol" --arg field "$field" \
                --argjson delta "$delta" "$manifest_extent_mutation" \
                "corpus/v1/$label/manifest.json"
            record "$name-manifest-save" cp -- "$output/commands/$name-manifest-mutate.stdout" \
                "$output/mutations/$name-manifest.json"
            gcc_manifest=corpus/v1/gcc/manifest.json
            clang_manifest=corpus/v1/clang/manifest.json
            if [[ $label == gcc ]]; then
                gcc_manifest=$output/mutations/$name-manifest.json
            else
                clang_manifest=$output/mutations/$name-manifest.json
            fi
            expect_status 1 "$name" report_json_with_manifests "$gcc_file" "$clang_file" \
                "$output/mutations/$name-report.json" "$gcc_manifest" "$clang_manifest"
            record "$name-stderr-empty" test ! -s "$output/commands/$name.stderr"
        done <<'MUTATIONS'
file_offset	1
address	1
size	-1
MUTATIONS
    done
done

# Flip the low bit of exactly one copied byte. Read the original byte first so
# the replacement cannot accidentally leave it unchanged. All destinations are
# fresh files within this run; never write an original or execute a mutation.
flip_byte() {
    local name=$1 original=$2 offset=$3 destination=$4 before after octal position
    local -a differences
    record "$name-copy" cp -- "$original" "$destination"
    record "$name-copy-identical" cmp -- "$original" "$destination"
    record "$name-original-byte" od -An -tu1 -j "$offset" -N 1 "$original"
    read -r before < "$output/commands/$name-original-byte.stdout"
    [[ $before =~ ^[0-9]+$ && $before -le 255 ]] || return 1
    after=$((before ^ 1))
    printf -v octal '\\%03o' "$after"
    record "$name-replacement-byte" printf '%b' "$octal"
    record "$name-write" dd "if=$output/commands/$name-replacement-byte.stdout" \
        "of=$destination" bs=1 "seek=$offset" conv=notrunc status=none
    expect_status 1 "$name-diff" cmp -l -- "$original" "$destination"
    mapfile -t differences < "$output/commands/$name-diff.stdout"
    record "$name-one-difference" test "${#differences[@]}" -eq 1
    read -r position _ < "$output/commands/$name-diff.stdout"
    record "$name-difference-position" test "$position" -eq "$((offset + 1))"
}

if [[ $full_project == true ]]; then
    # Exercise the installed data-only packet boundary, in addition to the
    # universal ELF/resource theorems. No candidate proof enters its snapshot.
    record scalar-grading-directory mkdir -p "$output/scalar-grading"
    while IFS=$'\t' read -r compiler operation task client theorem offset size; do
        base_label="scalar-$compiler-$operation"
        raw="$output/scalar-grading/$base_label.bin"
        record "$base_label-extract" dd "if=corpus/v1/$compiler/final.elf" "of=$raw" \
            bs=1 "skip=$offset" "count=$size" status=none
        modes=(body)
        if [[ $task == parity64 || $task == rotateLeft64 ]]; then
            modes+=(reference)
            record "$base_label-final-byte" od -An -tx1 -j "$((size - 1))" -N 1 "$raw"
            record "$base_label-final-ret" grep -Ex '[[:space:]]*c3[[:space:]]*' \
                "$output/commands/$base_label-final-byte.stdout"
        fi
        for mode in "${modes[@]}"; do
            label=$base_label
            options=(--body)
            if [[ $mode == reference ]]; then label=$base_label-reference; options=(); fi
            packet="$output/scalar-grading/$label.json"
            changed="$output/scalar-grading/$label-changed.bin"
            # No limit flags: both packet modes use the installed default
            # 300000-node / depth-128 checker and the same generic driver.
            record "$label-export" "${lean_lock[@]}" lake env .lake/build/bin/edsl-proof-export \
                "$client" "$theorem" "$packet" "${options[@]}"
            record "$label-grade" "${lean_lock[@]}" lake env .lake/build/bin/edsl-grade \
                "$task" "$raw" "$packet"
            wrong_task=absSigned32
            if [[ $task == absSigned32 ]]; then wrong_task=byteSwap64; fi
            if [[ $task == average64 ]]; then wrong_task=addModulo64; fi
            if [[ $task == parity64 ]]; then wrong_task=populationCount64; fi
            if [[ $task == rotateLeft64 ]]; then wrong_task=average64; fi
            expect_status 5 "$label-wrong-task" "${lean_lock[@]}" lake env .lake/build/bin/edsl-grade \
                "$wrong_task" "$raw" "$packet"
            record "$label-wrong-task-reason" grep -F 'kernel declTypeMismatch' \
                "$output/commands/$label-wrong-task.stderr"
            flip_byte "$label-change" "$raw" "$((size - 1))" "$changed"
            expect_status 5 "$label-changed-code" "${lean_lock[@]}" lake env .lake/build/bin/edsl-grade \
                "$task" "$changed" "$packet"
            record "$label-changed-code-reason" grep -F 'kernel declTypeMismatch' \
                "$output/commands/$label-changed-code.stderr"
        done
    done <<'SCALAR_GRADING'
gcc	rotation	rotateLeft64	tests.GradingRotation	EDSL.Tests.GradingRotation.raw_gcc	11744	13
clang	rotation	rotateLeft64	tests.GradingRotation	EDSL.Tests.GradingRotation.raw_clang	4944	9
gcc	parity	parity64	tests.GradingParity	EDSL.Tests.GradingParity.raw_gcc	11808	33
clang	parity	parity64	tests.GradingParity	EDSL.Tests.GradingParity.raw_clang	5008	36
gcc	absolute	absSigned32	tests.GradingUnary	EDSL.Tests.GradingUnary.raw_gcc_absolute	11632	12
clang	absolute	absSigned32	tests.GradingUnary	EDSL.Tests.GradingUnary.raw_clang_absolute	4864	8
gcc	reverse	byteSwap64	tests.GradingUnary	EDSL.Tests.GradingUnary.raw_gcc_reverse	11760	11
clang	reverse	byteSwap64	tests.GradingUnary	EDSL.Tests.GradingUnary.raw_clang_reverse	4960	7
gcc	popcount	populationCount64	tests.GradingPopcount	EDSL.Tests.GradingPopcount.raw_gcc	11776	31
clang	popcount	populationCount64	tests.GradingPopcount	EDSL.Tests.GradingPopcount.raw_clang	4976	28
gcc	average	average64	tests.GradingAverage	EDSL.Tests.GradingAverage.raw_gcc	11712	20
clang	average	average64	tests.GradingAverage	EDSL.Tests.GradingAverage.raw_clang	4928	16
SCALAR_GRADING
fi

record selected-offsets jq -r '.files[].certificates[0].file_offset' "$output/report.json"
mapfile -t offsets < "$output/commands/selected-offsets.stdout"
record addition-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_add_mod64").file_offset' "$output/report.json"
mapfile -t addition_offsets < "$output/commands/addition-offsets.stdout"
record clamp-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_clamp_i32").file_offset' "$output/report.json"
mapfile -t clamp_offsets < "$output/commands/clamp-offsets.stdout"
record buffer-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_strnlen_bytes").file_offset' "$output/report.json"
mapfile -t buffer_offsets < "$output/commands/buffer-offsets.stdout"
record search-byte-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_memchr_index").file_offset' "$output/report.json"
mapfile -t search_byte_offsets < "$output/commands/search-byte-offsets.stdout"
record search-u32-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_linear_search_u32").file_offset' "$output/report.json"
mapfile -t search_u32_offsets < "$output/commands/search-u32-offsets.stdout"
record byte-comparison-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_memcmp_bytes").file_offset' "$output/report.json"
mapfile -t byte_comparison_offsets < "$output/commands/byte-comparison-offsets.stdout"
record average-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_average_u64").file_offset' "$output/report.json"
mapfile -t average_offsets < "$output/commands/average-offsets.stdout"
record parity-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_parity_loop").file_offset' "$output/report.json"
mapfile -t parity_offsets < "$output/commands/parity-offsets.stdout"
record rotation-offsets jq -r '.files[].certificates[] |
    select(.symbol == "c_rotl64").file_offset' "$output/report.json"
mapfile -t rotation_offsets < "$output/commands/rotation-offsets.stdout"
gcc_code=$output/mutations/gcc-code-byte.elf
clang_code=$output/mutations/clang-code-byte.elf
gcc_addition=$output/mutations/gcc-addition-code-byte.elf
clang_addition=$output/mutations/clang-addition-code-byte.elf
gcc_clamp=$output/mutations/gcc-clamp-code-byte.elf
clang_clamp=$output/mutations/clang-clamp-code-byte.elf
gcc_buffer=$output/mutations/gcc-buffer-code-byte.elf
clang_buffer=$output/mutations/clang-buffer-code-byte.elf
gcc_search_byte=$output/mutations/gcc-search-byte-code-byte.elf
clang_search_byte=$output/mutations/clang-search-byte-code-byte.elf
gcc_search_u32=$output/mutations/gcc-search-u32-code-byte.elf
clang_search_u32=$output/mutations/clang-search-u32-code-byte.elf
gcc_byte_comparison=$output/mutations/gcc-byte-comparison-code-byte.elf
clang_byte_comparison=$output/mutations/clang-byte-comparison-code-byte.elf
gcc_average=$output/mutations/gcc-average-code-byte.elf
clang_average=$output/mutations/clang-average-code-byte.elf
gcc_parity=$output/mutations/gcc-parity-code-byte.elf
clang_parity=$output/mutations/clang-parity-code-byte.elf
gcc_rotation=$output/mutations/gcc-rotation-code-byte.elf
clang_rotation=$output/mutations/clang-rotation-code-byte.elf
gcc_metadata=$output/mutations/gcc-metadata-byte.elf
gcc_comment=$output/mutations/gcc-comment-byte.elf
gcc_truncated=$output/mutations/gcc-truncated.elf
gcc_appended=$output/mutations/gcc-appended.elf
flip_byte gcc-code "$gcc_file" "${offsets[0]}" "$gcc_code"
reject 1 reject-gcc-code --gcc "$gcc_code"
flip_byte clang-code "$clang_file" "${offsets[1]}" "$clang_code"
# GCC stays valid: this control catches a validator that checks only GCC.
reject 1 reject-clang-code --clang "$clang_code"
flip_byte gcc-addition-code "$gcc_file" "${addition_offsets[0]}" "$gcc_addition"
reject 1 reject-gcc-addition-code --gcc "$gcc_addition"
flip_byte clang-addition-code "$clang_file" "${addition_offsets[1]}" "$clang_addition"
# GCC is still valid, so a later Clang addition mismatch must emit no report.
reject 1 reject-clang-addition-code --clang "$clang_addition"
flip_byte gcc-clamp-code "$gcc_file" "${clamp_offsets[0]}" "$gcc_clamp"
reject 1 reject-gcc-clamp-code --gcc "$gcc_clamp"
flip_byte clang-clamp-code "$clang_file" "${clamp_offsets[1]}" "$clang_clamp"
# The accepted GCC file must not mask a later Clang clamp mismatch.
reject 1 reject-clang-clamp-code --clang "$clang_clamp"
flip_byte gcc-buffer "$gcc_file" "${buffer_offsets[0]}" "$gcc_buffer"
reject 1 reject-gcc-buffer-code --gcc "$gcc_buffer"
flip_byte clang-buffer "$clang_file" "${buffer_offsets[1]}" "$clang_buffer"
reject 1 reject-clang-buffer-code --clang "$clang_buffer"
flip_byte gcc-search-byte "$gcc_file" "${search_byte_offsets[0]}" "$gcc_search_byte"
reject 1 reject-gcc-search-byte-code --gcc "$gcc_search_byte"
flip_byte clang-search-byte "$clang_file" "${search_byte_offsets[1]}" "$clang_search_byte"
reject 1 reject-clang-search-byte-code --clang "$clang_search_byte"
flip_byte gcc-search-u32 "$gcc_file" "${search_u32_offsets[0]}" "$gcc_search_u32"
reject 1 reject-gcc-search-u32-code --gcc "$gcc_search_u32"
flip_byte clang-search-u32 "$clang_file" "${search_u32_offsets[1]}" "$clang_search_u32"
reject 1 reject-clang-search-u32-code --clang "$clang_search_u32"
flip_byte gcc-byte-comparison "$gcc_file" "${byte_comparison_offsets[0]}" "$gcc_byte_comparison"
reject 1 reject-gcc-byte-comparison-code --gcc "$gcc_byte_comparison"
flip_byte clang-byte-comparison "$clang_file" "${byte_comparison_offsets[1]}" "$clang_byte_comparison"
reject 1 reject-clang-byte-comparison-code --clang "$clang_byte_comparison"
flip_byte gcc-average "$gcc_file" "${average_offsets[0]}" "$gcc_average"
reject 1 reject-gcc-average-code --gcc "$gcc_average"
flip_byte clang-average "$clang_file" "${average_offsets[1]}" "$clang_average"
# The unchanged GCC image must not hide a changed Clang average body.
reject 1 reject-clang-average-code --clang "$clang_average"
flip_byte gcc-parity "$gcc_file" "${parity_offsets[0]}" "$gcc_parity"
reject 1 reject-gcc-parity-code --gcc "$gcc_parity"
flip_byte clang-parity "$clang_file" "${parity_offsets[1]}" "$clang_parity"
reject 1 reject-clang-parity-code --clang "$clang_parity"
flip_byte gcc-rotation "$gcc_file" "${rotation_offsets[0]}" "$gcc_rotation"
reject 1 reject-gcc-rotation-code --gcc "$gcc_rotation"
flip_byte clang-rotation "$clang_file" "${rotation_offsets[1]}" "$clang_rotation"
reject 1 reject-clang-rotation-code --clang "$clang_rotation"

# ELF identification byte 8 is inside each complete file but outside every
# certified function. Keep this header-field control alongside the opaque
# .comment control below, which exercises complete-file identity independently.
record metadata-offset-outside-code jq -e \
    'all(.files[]; .bytes > 8 and all(.certificates[];
      8 < .file_offset or 8 >= .file_offset + .size))' "$output/report.json"
flip_byte gcc-metadata "$gcc_file" 8 "$gcc_metadata"
gcc_body_selection=$(cat <<'JQ'
    .functions[] |
    select(.symbol as $symbol | any($report[0].files[0].certificates[]; .symbol == $symbol)) |
    [.file_offset, .size] | @tsv
JQ
)
record gcc-body-spans jq -r --slurpfile report "$output/report.json" \
    "$gcc_body_selection" corpus/v1/gcc/manifest.json
record certified-span-count jq -er '.score.functions_certified_end_to_end' "$output/report.json"
read -r certified_span_count < "$output/commands/certified-span-count.stdout"
span=0
while IFS=$'\t' read -r offset size; do
    record "metadata-code-span-$span-unchanged" cmp "--ignore-initial=$offset:$offset" \
        "--bytes=$size" -- "$gcc_file" "$gcc_metadata"
    span=$((span + 1))
done < "$output/commands/gcc-body-spans.stdout"
record all-metadata-code-spans-checked test "$span" -eq "$certified_span_count"
reject 1 reject-gcc-metadata --gcc "$gcc_metadata"

# Locate the opaque compiler-identification payload by section-name token:
# readelf's bracket spacing varies, so fixed column numbers are unsuitable.
# Reject missing/duplicate/empty/out-of-bounds sections. Strip leading zeroes
# and limit significant hex digits before using signed shell arithmetic.
record gcc-sections readelf -SW "$gcc_file"
# Keep awk field expressions literal for awk, rather than the shell.
# shellcheck disable=SC2016
record gcc-comment-section awk '
  {
    for (i = 1; i <= NF; i++) {
      if ($i == ".comment") {
        count++;
        if (i + 4 > NF || $(i + 1) != "PROGBITS") invalid = 1;
        offset = $(i + 3); size = $(i + 4);
      }
    }
  }
  END {
    if (count != 1 || invalid || offset !~ /^[0-9a-fA-F]+$/ ||
        size !~ /^[0-9a-fA-F]+$/) exit 1;
    sub(/^0+/, "", offset); sub(/^0+/, "", size);
    if (offset == "") offset = "0";
    if (size == "") size = "0";
    if (length(offset) > 15 || length(size) > 15) exit 1;
    printf "%s\t%s\n", offset, size;
  }' "$output/commands/gcc-sections.stdout"
read -r comment_offset_hex comment_size_hex < "$output/commands/gcc-comment-section.stdout"
comment_offset=$((16#$comment_offset_hex))
comment_size=$((16#$comment_size_hex))
record gcc-comment-decimal printf '%s\t%s\n' "$comment_offset" "$comment_size"
record gcc-comment-nonempty test "$comment_size" -gt 0
record gcc-comment-offset-in-file test "$comment_offset" -lt "$gcc_size"
record gcc-comment-size-in-file test "$comment_size" -le "$((gcc_size - comment_offset))"
# jq receives offset and size through --argjson, not shell interpolation.
comment_code_selection=$(cat <<'JQ'
    [.functions[] | select(.symbol as $symbol |
      any($report[0].files[0].certificates[]; .symbol == $symbol))] |
    length == $report[0].score.functions_certified_end_to_end and all(.[];
      $offset + $size <= .file_offset or $offset >= .file_offset + .size)
JQ
)
record gcc-comment-outside-code jq -e --argjson offset "$comment_offset" \
    --argjson size "$comment_size" --slurpfile report "$output/report.json" "$comment_code_selection" \
    corpus/v1/gcc/manifest.json
flip_byte gcc-comment "$gcc_file" "$comment_offset" "$gcc_comment"
record gcc-comment-file-size wc -c "$gcc_comment"
read -r comment_file_size _ < "$output/commands/gcc-comment-file-size.stdout"
record gcc-comment-length-unchanged test "$comment_file_size" -eq "$gcc_size"
span=0
while IFS=$'\t' read -r offset size; do
    record "comment-code-span-$span-unchanged" cmp "--ignore-initial=$offset:$offset" \
        "--bytes=$size" -- "$gcc_file" "$gcc_comment"
    span=$((span + 1))
done < "$output/commands/gcc-body-spans.stdout"
record all-comment-code-spans-checked test "$span" -eq "$certified_span_count"
reject 1 reject-gcc-comment --gcc "$gcc_comment"

record truncate-copy cp -- "$gcc_file" "$gcc_truncated"
record truncate-copy-identical cmp -- "$gcc_file" "$gcc_truncated"
record truncate-one-byte truncate -s "$((gcc_size - 1))" "$gcc_truncated"
expect_status 1 truncated-diff cmp -s -- "$gcc_file" "$gcc_truncated"
record truncated-size wc -c "$gcc_truncated"
read -r truncated_size _ < "$output/commands/truncated-size.stdout"
record truncated-length test "$truncated_size" -eq "$((gcc_size - 1))"
reject 1 reject-gcc-truncated --gcc "$gcc_truncated"
# A complete-file comparison must also reject an unchanged accepted prefix with
# one extra byte, independently of the truncated-file control above.
record append-copy cp -- "$gcc_file" "$gcc_appended"
record append-copy-identical cmp -- "$gcc_file" "$gcc_appended"
record append-byte printf '\001'
record append-write dd "if=$output/commands/append-byte.stdout" "of=$gcc_appended" \
    bs=1 "seek=$gcc_size" conv=notrunc status=none
record appended-size wc -c "$gcc_appended"
read -r appended_size _ < "$output/commands/appended-size.stdout"
record appended-length test "$appended_size" -eq "$((gcc_size + 1))"
record appended-prefix-identical cmp "--bytes=$gcc_size" -- "$gcc_file" "$gcc_appended"
expect_status 1 appended-diff cmp -s -- "$gcc_file" "$gcc_appended"
reject 1 reject-gcc-appended --gcc "$gcc_appended"
expect_status 1 wrong-compiler-diff cmp -s -- "$gcc_file" "$valid_clang"
reject 1 reject-wrong-compiler --gcc "$valid_clang"

record missing-path-absent test ! -e "$output/mutations/missing.elf"
reject 3 reject-missing-file --gcc "$output/mutations/missing.elf"
reject 3 reject-missing-clang --clang "$output/mutations/missing.elf"
reject 2 reject-unknown-flag --unknown "$valid_gcc"
reject 2 reject-missing-argument --gcc
reject 2 reject-missing-clang-argument --clang
reject 2 reject-gcc-option-value --gcc --clang
reject 2 reject-clang-option-value --clang --gcc
reject 2 reject-adjacent-duplicate-gcc --gcc --gcc
reject 2 reject-empty-gcc --gcc ''
reject 2 reject-empty-clang --clang ''
reject 2 reject-duplicate-gcc --gcc "$valid_gcc" --gcc "$valid_gcc"
reject 2 reject-duplicate-clang --clang "$valid_clang" --clang "$valid_clang"
reject 2 reject-positional "$valid_gcc"

# Run structural, serialization and installed-admission controls before paying
# for the full fresh replay. Replay is still mandatory for gate success; the
# original source, object and tool pins remain in force through this stage.
record "$fresh_label" "${lean_env[@]}" leanchecker --fresh "$fresh_target"
complete=true
# EXIT performs the final source, frozen-file, imported-module and gate-input
# stability checks before it creates READY.md or emits a gate success message.
