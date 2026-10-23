#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# The caller/master holds /tmp/edsl-lean-build.lock throughout this script.
# Do not acquire that lock here. Artifact files are read as data, never run.
set -euo pipefail
umask 022
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH" LC_ALL=C TZ=UTC LEAN_NUM_THREADS=1
if [[ $# != 3 ]]; then
    echo 'usage: scripts/check-call-memory-loop64-grading.sh OUTPUT GCC_TEXT CLANG_TEXT' >&2
    exit 2
fi
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
inputs=("$2" "$3")

# Admission precedes every write, including mkdir for an existing OUTPUT.
# In-checkout evidence must be ignored so it cannot change the public snapshot.
output_error() {
    printf 'Counted DATA8 grading: %s; refusing OUTPUT without writes\n' "$1" >&2
    exit 2
}
candidate=$1
[[ ! -L $candidate ]] || output_error 'OUTPUT must be an empty real directory'
output=$(realpath -m -- "$candidate" 2>/dev/null) ||
    output_error 'cannot resolve OUTPUT'
if [[ $output == "$PWD" || $PWD == "$output/"* ]]; then
    output_error 'OUTPUT must not contain the source checkout'
fi
if [[ $output == "$PWD/"* ]] && ! git check-ignore -q -- "$output"; then
    output_error 'in-checkout OUTPUT must be ignored by git'
fi
if [[ -e $output ]]; then
    [[ -d $output && ! -L $output ]] ||
        output_error 'OUTPUT must be an empty real directory'
    [[ -r $output && -w $output && -x $output ]] ||
        output_error 'OUTPUT must be a readable writable searchable empty directory'
    permissions=$(stat -c %a -- "$output" 2>/dev/null) ||
        output_error 'cannot inspect OUTPUT permissions'
    # Also reject mode-000 directories when invoked by a privileged caller.
    if [[ ! $permissions =~ ^[0-7]+$ ]] ||
        (( (8#$permissions & 0444) == 0 || (8#$permissions & 0222) == 0 ||
           (8#$permissions & 0111) == 0 )); then
        output_error 'OUTPUT must be a readable writable searchable empty directory'
    fi
    existing=$(find "$output" -mindepth 1 -maxdepth 1 -print -quit 2>/dev/null) ||
        output_error 'OUTPUT must be a readable empty directory'
    [[ -z $existing ]] || output_error 'OUTPUT must be an empty real directory'
else
    if ! mkdir -p -- "${output%/*}" || ! mkdir -- "$output"; then
        output_error 'cannot create OUTPUT'
    fi
fi

profiles=(gccSeparate clangSeparate)
compiler_names=(gcc13 clang18)
client_modules=(tests.fixtures.CallMemoryLoop64.GCC tests.fixtures.CallMemoryLoop64.Clang)
client_claims=(EDSL.CallMemoryLoop64.GCC.claim EDSL.CallMemoryLoop64.Clang.claim)
lengths=(45 52)
helper_offsets=(38 45)
call_offsets=(20 24)
caller_rets=(37 44)
helper_rets=(44 51)
closed_lengths=(17 19)
closed_stores=(13 15)
closed_claims=(EDSL.CallMemoryLoop64.ClosedForm.Exported.gcc
    EDSL.CallMemoryLoop64.ClosedForm.Exported.clang)
phases=(sources script-checks tools build audits installation nested-artifacts
    closed-form-artifacts nested-packets closed-form-packets nested-grades
    closed-form-grades protocol negatives container-reuse isolation
    source-stability input-stability installation-stability evidence-closure)
declare -A phase_status receipt_seen
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
phase=setup
sequence=0 failures=0 phase_start_failures=0
suite_complete=false command_ok=false case_ok=false
nested_accepts=0 closed_form_accepts=0 container_accepts=0 poisoned_accepts=0
reference_rejections=0
packet_ready=(false false)
closed_ready=(false false)
source_ready=false installation_ready=false
lean_prefix=
stability_receipts=()
required_receipts=()
for index in 0 1; do
    required_receipts+=("$output/nested/${profiles[index]}/original-SHA256SUMS"
        "$output/nested/${profiles[index]}/artifact-SHA256SUMS"
        "$output/closed-form/${compiler_names[index]}/artifact-SHA256SUMS"
        "$output/packets/${profiles[index]}.json.SHA256SUMS"
        "$output/packets/closed-form-${compiler_names[index]}.json.SHA256SUMS"
        "$output/nested/${profiles[index]}/container-note/artifact-SHA256SUMS")
done
exec 6>&2

run() {
    sequence=$((sequence + 1))
    local status=0 line arguments tag="$BASHPID.$sequence"
    printf -v arguments '%q ' "$@"
    printf -v line '[%s] phase=%s cwd=%q argv=%s\n' "$tag" "$phase" "$PWD" "$arguments"
    # One write per record. BASHPID distinguishes command-substitution counters.
    printf '%s' "$line" >&3
    "$@" || status=$?
    printf '%s\t%s\t%d\n' "$tag" "$phase" "$status" >&4
    return "$status"
}
failure() {
    failures=$((failures + 1))
    printf 'Counted DATA8 grading: %s (see %s)\n' "$1" "$output" >&6
}
checked() {
    local status=0
    run "$@" || status=$?
    command_ok=false
    if [[ $status == 0 ]]; then command_ok=true
    else failure "command failed: $1 (exit=$status)"; fi
    # Independent phases still close after an earlier dependency fails.
    return 0
}
write_phases() {
    local name
    printf 'phase\tresult\n' > "$output/phase-status.tsv"
    for name in "${phases[@]}"; do
        printf '%s\t%s\n' "$name" "${phase_status[$name]}" >> "$output/phase-status.tsv"
    done
}
begin_phase() {
    phase=$1
    phase_start_failures=$failures
    phase_status[$phase]=RUNNING
    write_phases
    printf 'grading_phase=%s status=RUNNING UTC=%s\n' "$phase" "$(date -u +%FT%TZ)" >&2
}
end_phase() {
    if [[ $failures == "$phase_start_failures" ]]; then phase_status[$phase]=PASS
    else phase_status[$phase]=FAIL; fi
    write_phases
}
manifest() {
    (
        cd -- "$output" || exit 1
        # Exclude only the root checksum files and their enumeration input.
        # In particular, retain every nested checksum receipt and failure log.
        # shellcheck disable=SC2094
        find . -type f ! -path ./SHA256SUMS ! -path ./MANIFEST-SHA256.txt \
            ! -path ./manifest-inputs.list0 -print0 | sort -z > manifest-inputs.list0 || exit 1
        xargs -0 -r sha256sum -- < manifest-inputs.list0 > SHA256SUMS || exit 1
        sha256sum manifest-inputs.list0 >> SHA256SUMS || exit 1
        sha256sum SHA256SUMS > MANIFEST-SHA256.txt
    )
}
write_terminal() {
    local status=$1 result=$2
    write_phases
    printf 'grading=%s nested_raw_elf=%d/4 closed_form_raw_elf=%d/4 fast_native=NOTRUN native_observations=NESTED_ONLY container_reuse=%d/2 poisoned_raw_elf=%d/8 reference_only=%d/8 failures=%d\n' \
        "$result" "$nested_accepts" "$closed_form_accepts" "$container_accepts" \
        "$poisoned_accepts" "$reference_rejections" "$failures" > "$output/result.txt"
    printf 'exit=%d UTC=%s final_phase=%s complete=%s\n' \
        "$status" "$(date -u +%FT%TZ)" "$phase" "$suite_complete" > "$output/terminal-status.txt"
}
finish() {
    local status=$? name result=FAIL
    trap - EXIT HUP INT TERM
    set +e
    for name in "${phases[@]}"; do
        if [[ ${phase_status[$name]} == RUNNING ]]; then phase_status[$name]=FAIL; fi
    done
    if [[ $status == 0 && $failures == 0 ]] && $suite_complete; then
        result=PASS
        for name in "${phases[@]}"; do
            if [[ ${phase_status[$name]} != PASS ]]; then result=FAIL; fi
        done
        if (( nested_accepts != 4 || closed_form_accepts != 4 || container_accepts != 2 ||
              poisoned_accepts != 8 || reference_rejections != 8 ||
              ${#stability_receipts[@]} != 12 )); then result=FAIL; fi
    fi
    if [[ $result != PASS && $status == 0 ]]; then status=1; fi
    if ! write_terminal "$status" "$result"; then status=1; result=FAIL; fi
    exec 3>&- 4>&- 5>&- 6>&-
    if ! manifest; then
        status=1 result=FAIL
        failures=$((failures + 1))
        write_terminal "$status" "$result"
        printf 'Evidence manifest failed\n' > "$output/manifest-error.txt"
        manifest
    fi
    printf 'Counted DATA8 grading: %s; evidence=%s\n' "$result" "$output" >&2
    exit "$status"
}
trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
exec 3>"$output/commands.log" 4>"$output/command-status.tsv" 5>"$output/case-status.tsv"
printf 'tag\tphase\texit\n' >&4
printf 'case\tcategory\texpected\tobserved\tresult\tdiagnostic\n' >&5

# One new CLI process per candidate. Kernel heartbeats accumulate per thread.
# Exact status and the COMPLETE stdout/stderr are required. Resource exit 6,
# timeout, signal and I/O failures never satisfy a semantic rejection.
expect_case() {
    local expected=$1 reason=$2 name=$3 category=$4 status=0 result=FAIL
    shift 4
    local directory="$output/cases/$name"
    local -a lines=()
    mkdir -p -- "$directory"
    printf '%s\n' "$reason" > "$directory/expected-diagnostic.txt"
    run timeout --signal=TERM --kill-after=5s 60s "$@" \
        > "$directory/stdout.txt" 2> "$directory/stderr.txt" || status=$?
    printf '%d\n' "$status" > "$directory/exit-status.txt"
    case_ok=false
    if [[ $status == "$expected" ]]; then
        if [[ $expected == 0 ]]; then
            mapfile -t lines < "$directory/stdout.txt"
            if [[ ! -s $directory/stderr.txt && ${#lines[@]} == 1 && ${lines[0]} =~ $reason ]]; then
                printf '%s\n' "${lines[0]}" > "$directory/expected-stdout.txt"
                if run cmp -s "$directory/expected-stdout.txt" "$directory/stdout.txt"; then case_ok=true; fi
            fi
        elif [[ ! -s $directory/stdout.txt ]] &&
            run cmp -s "$directory/expected-diagnostic.txt" "$directory/stderr.txt"; then
            case_ok=true
        fi
    fi
    if $case_ok; then result=PASS; else failure "$name expected=$expected observed=$status"; fi
    printf '%s\t%s\t%d\t%d\t%s\t%s\n' "$name" "$category" "$expected" "$status" "$result" "$reason" >&5
}
unavailable() {
    printf '%s\tdependency\t-\tNOTRUN\tFAIL\t%s\n' "$1" "$2" >&5
    failure "$1: $2"
}
accept() {
    local name=$1 length=$2
    shift 2
    expect_case 0 "^ACCEPTED: fixed counted DATA8 contract, exact artifact, selected entry and current OS resources; codeBytes=$length, auxiliaryDeclarations=[0-9]+, decoderSteps=[0-9]+, kernelChecks=[0-9]+$" \
        "$name" acceptance "$@"
}
remember_hashes() {
    local receipt=$1
    shift
    if [[ ${receipt_seen[$receipt]:-false} == true ]]; then
        failure "duplicate hash receipt: $receipt"
        return
    fi
    checked sha256sum -- "$@" > "$receipt" 2> "$receipt.stderr"
    if $command_ok; then
        stability_receipts+=("$receipt")
        receipt_seen[$receipt]=true
    fi
}
public_snapshot() {
    local prefix=$1 source
    run git ls-files --cached --others --exclude-standard -z -- . > "$prefix.git-files.list0" || return
    run sort -zu "$prefix.git-files.list0" > "$prefix.files.list0" || return
    [[ -s $prefix.files.list0 ]] || return 1
    : > "$prefix.regular-files.list0"
    while IFS= read -r -d '' source; do
        if [[ -L $source ]]; then continue; fi
        if [[ ! -f $source ]]; then
            printf 'Public source missing or unsupported: %q\n' "$source" >&2
            return 1
        fi
        printf '%s\0' "$source" >> "$prefix.regular-files.list0"
    done < "$prefix.files.list0"
    run xargs -0 -r sha256sum -- < "$prefix.regular-files.list0" > "$prefix.file-SHA256SUMS" || return
    # Tar preserves modes and symlink targets (including dangling links), with
    # canonical metadata instead of mtime/uid noise. Never dereference links.
    run tar --format=gnu --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
        --null --verbatim-files-from --no-recursion -T "$prefix.files.list0" -cf "$prefix.tar" || return
    run sha256sum -- "$prefix.tar" > "$prefix.SHA256SUMS"
}
installation_snapshot() {
    local prefix=$1
    [[ -n $lean_prefix ]] || return 1
    run find .lake/build "$lean_prefix" \( -type f -o -type l \) \
        \( -name '*.olean' -o -name '*.private' -o -name '*.server' \
        -o -name '*.so' -o -name '*.so.*' \) -print0 > "$prefix.unsorted.list0" || return
    run find .lake/build/bin "$lean_prefix/bin" \( -type f -o -type l \) -print0 \
        >> "$prefix.unsorted.list0" || return
    run sort -zu "$prefix.unsorted.list0" > "$prefix.files.list0" || return
    [[ -s $prefix.files.list0 ]] || return 1
    run xargs -0 -r sha256sum -- < "$prefix.files.list0" > "$prefix.SHA256SUMS" || return
    run xargs -0 -r stat -c '%a %F %N' -- < "$prefix.files.list0" > "$prefix.metadata.txt"
}
inspect_artifact() {
    local directory=$1 length=$2
    checked stat -c %s -- "$directory/text.bin" > "$directory/span.txt" 2> "$directory/stat.stderr"
    if [[ $(< "$directory/span.txt") != "$length" ]]; then failure "$directory: expected $length whole text bytes"; fi
    checked /usr/bin/objcopy -O binary --only-section=.text "$directory/function.elf" "$directory/extracted-text.bin" \
        > "$directory/extraction.log" 2>&1
    checked cmp "$directory/text.bin" "$directory/extracted-text.bin" > "$directory/extraction-binding.log" 2>&1
    checked /usr/bin/readelf -aW "$directory/function.elf" > "$directory/readelf.txt" 2>&1
    checked /usr/bin/readelf -rW "$directory/function.elf" > "$directory/relocations.txt" 2>&1
    checked grep -Fxq 'There are no relocations in this file.' "$directory/relocations.txt"
    checked /usr/bin/objdump -drwC -Mintel --show-raw-insn "$directory/function.elf" > "$directory/disassembly.txt" 2>&1
    checked od -An -v -tx1 "$directory/text.bin" > "$directory/text.hex" 2>&1
}

rejected='EDSLGrader.Runtime.FailureKind.rejected: kernel declTypeMismatch; no defect conclusion'
unsupported='EDSLGrader.Runtime.FailureKind.unsupported: counted DATA8 artifact admission failed; no defect conclusion'
unknown='EDSLGrader.Runtime.FailureKind.malformed: unknown constant; no defect conclusion'
resource='EDSLGrader.Runtime.FailureKind.resource: file bytes; no defect conclusion'
internal='internal: IO or trusted installation failure; no defect conclusion'
usage='usage: edsl-grade-call-memory-loop64 [--elf SPAN_BYTES] ENTRY_OFFSET INPUT PROOF.json; no defect conclusion'
export_pattern='^EXPORTED: client packet; auxiliaryDeclarations=[1-9][0-9]*, declaredNames=[1-9][0-9]*, bytes=[1-9][0-9]*\. Submit to the matching fixed-contract grader for artifact checking\.$'
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade-call-memory-loop64)

begin_phase sources
mkdir -p "$output/metadata" "$output/nested" "$output/closed-form" "$output/packets" "$output/negative"
checked git rev-parse HEAD > "$output/metadata/HEAD.txt" 2>&1
checked git status --short --branch --untracked-files=all > "$output/metadata/worktree.txt" 2>&1
if public_snapshot "$output/public-source" > "$output/source-snapshot.log" 2>&1; then source_ready=true
else failure 'initial public source snapshot failed'; fi
cat > "$output/scope.txt" <<'SCOPE'
Project-owned synthetic counted DATA8 artifacts only, never executed here.
The authenticated parent raw inputs and complete sibling function.elf files
are copied as DATA: GCC13 45 bytes, entry0/helper38/CALL20/callerRET37/helperRET44;
Clang18 52 bytes, entry0/helper45/CALL24/callerRET44/helperRET51. The parent owns
all nested native observations. No native observations of closed-form code are
made or claimed by this runner.

Fresh GNU23 -Os compilation of call-memory-loop64-closed-form.c uses the exact
unchanged parent flags and caller entry/link address. GCC13's 17-byte leaf and
Clang18's 19-byte leaf have no helper. Four independently exported client
packets must pass eight raw/full-ELF grades at existing default limits under
the SAME independent root CallMemoryLoop64.Claim. Results cover all full64 x/n
including n=0, x+n modulo 2^64, old DATA if n=0 and x+n-1 otherwise, useful
current DATA/private-stack capacity at least32, ABI and union RAM frame.
Admission has no CALL/read/count whitelist, cost or future-execution premise.
Separate nested and closed-form model-cost theorems are audited as conclusions,
never used as admission filters.

Only the exporter imports the named built client. All controllers use the
fixed installed environment and default budgets. Its eight foundations are
EDSL, EDSL.Grading.Known, EDSL.Grading.Artifact, EDSL.Grading.CallStack.Artifact,
EDSL.Grading.CallMemory64.Artifact, EDSL.Grading.CallMemoryLoop64.Artifact,
EDSL.Grading.AtomicLogical64.Artifact and EDSL.Grading.AtomicSet64.Artifact,
matching the exporter's fixed snapshot. No client fixture is foundational.
Every candidate invocation is a fresh CLI process with a cumulative kernel
heartbeat ceiling. Plain and poisoned reference-only packets must fail for
all four client names; serialized packets must accept raw and ELF in poison.
Poison covers all eight foundations and GCC, Clang, ClosedForm and Exports.

The same program proof may accept a different nonloaded ELF container: each
grade checks a new exact-file literal wrapper. Two nonloaded note additions
must accept, independently of selected-code/entry/span/backing negatives.
Exact exit status and complete stdout/stderr distinguish semantic rejection,
unsupported admission, malformed protocol, resource limits and I/O failures.
No timeout, signal, resource or I/O error counts as semantic rejection. An
unsuccessful proof establishes no defect.

Canonical public snapshots cover tracked and nonignored untracked files,
including modes and symlinks, with HEAD stability. Original/copy inputs,
fresh compiler objects/ELFs/text, all four packets and alternate containers
have twelve mandatory hash receipts. Project and sysroot Lean objects,
private/server companions, shared libraries and tool binaries are checked
before and after grading. Commands, exact statuses, phase/case closure and
failure evidence are retained in a complete final manifest.
The caller holds the Lean build lock; this runner never acquires it.
Environmental assumptions remain those of the pinned trusted installation
and fixed Lean contract (ordinary RAM, AC/CET disabled and no asynchronous
interference). This is not compiler preservation, native CPU correspondence
or a Linux process-startup proof.
SCOPE
end_phase

begin_phase script-checks
checked bash -n scripts/check-call-memory-loop64-grading.sh > "$output/bash-n.log" 2>&1
checked shellcheck -s bash scripts/check-call-memory-loop64-grading.sh > "$output/shellcheck.log" 2>&1
printf '%s\n' EDSL EDSL.Grading.Known EDSL.Grading.Artifact \
    EDSL.Grading.CallStack.Artifact EDSL.Grading.CallMemory64.Artifact \
    EDSL.Grading.CallMemoryLoop64.Artifact EDSL.Grading.AtomicLogical64.Artifact \
    EDSL.Grading.AtomicSet64.Artifact \
    > "$output/metadata/expected-foundations.txt"
# Compare actual fixed import arrays against the installation policy, stopping
# before the exporter imports its separate client. A fixture added to either
# trusted snapshot must fail even if it does not define our four entry names.
for controller in driver exporter; do
    if [[ $controller == driver ]]; then
        controller_source=EDSL/Grading/Driver.lean
        controller_entry='def trustedEnvironment'
        controller_stop='def readBounded'
    else
        controller_source=EDSL/Grading/Export.lean
        controller_entry='def loadEnvironments'
        controller_stop='  let client'
    fi
    # shellcheck disable=SC2016
    checked awk -v entry="$controller_entry" -v stop="$controller_stop" '
        index($0, entry) == 1 { active = 1 }
        active && index($0, stop) == 1 { exit }
        active {
            line = $0
            while (match(line, /module := [^ }]+/)) {
                token = substr(line, RSTART, RLENGTH)
                sub(/^module := ./, "", token)
                print token
                line = substr(line, RSTART + RLENGTH)
            }
        }' "$controller_source" > "$output/metadata/$controller-foundations.txt" \
        2> "$output/metadata/$controller-foundations.stderr"
    checked cmp "$output/metadata/expected-foundations.txt" "$output/metadata/$controller-foundations.txt" \
        > "$output/metadata/$controller-foundations-binding.log" 2>&1
done
for controller_source in Tools/Grade/Function.lean Tools/Grade/CallStack.lean Tools/Grade/CallMemory64.lean \
    Tools/Grade/CallMemoryLoop64.lean Tools/Grade/AtomicLogical64.lean Tools/Grade/AtomicSet64.lean; do
    if [[ $controller_source == Tools/Grade/Function.lean ]]; then
        # The registered CLI keeps legacy packets in the original snapshot.
        checked grep -Fxq '    let env ← match id with' "$controller_source"
        checked grep -Fxq '      | .legacy _ => trustedEnvironment' "$controller_source"
        checked grep -Fxq '      | .multiplyModulo64 => trustedRegistryEnvironment' "$controller_source"
    else
        checked grep -Fq 'let env ← trustedEnvironment' "$controller_source"
    fi
    checked grep -Fq 'let limits : Limits := {}' "$controller_source"
done
end_phase

begin_phase tools
{
    checked date -u +%FT%TZ
    checked uname -a
    checked cat /etc/os-release lean-toolchain
    checked lake --version
    checked lake env lean --version
    checked /usr/bin/gcc-13 --version
    checked /usr/bin/gcc-13 -dumpfullversion
    checked /usr/bin/gcc-13 -dumpmachine
    checked /usr/bin/clang-18 --version
    checked /usr/bin/clang-18 -print-target-triple
    for tool in ld as objcopy readelf objdump nm shellcheck timeout jq; do checked "/usr/bin/$tool" --version; done
} > "$output/metadata/tools.txt" 2>&1
checked /usr/bin/gcc-13 -dumpfullversion > "$output/metadata/gcc-version.txt" 2>&1
checked /usr/bin/clang-18 --version > "$output/metadata/clang-version.txt" 2>&1
checked grep -Eq '^13\.' "$output/metadata/gcc-version.txt"
checked grep -Eq 'clang version 18\.' "$output/metadata/clang-version.txt"
checked lake env lean --version > "$output/metadata/lean-version.txt" 2>&1
if [[ $(< lean-toolchain) == leanprover/lean4:v4.35.0 ]]; then
    checked grep -Fq 'version 4.35.0,' "$output/metadata/lean-version.txt"
else failure 'expected pinned Lean 4.35.0'; fi
checked lake env lean --print-prefix > "$output/metadata/lean-prefix.txt" 2> "$output/metadata/lean-prefix.stderr"
if $command_ok; then
    lean_prefix=$(< "$output/metadata/lean-prefix.txt")
    checked readlink -f -- "$lean_prefix" > "$output/metadata/lean-prefix-real.txt" 2>&1
    if $command_ok; then lean_prefix=$(< "$output/metadata/lean-prefix-real.txt"); else lean_prefix=; fi
fi
checked /usr/bin/gcc-13 -print-prog-name=cc1 > "$output/metadata/gcc-cc1.txt" 2>&1
compiler_frontend=$(< "$output/metadata/gcc-cc1.txt")
checked sha256sum /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as \
    /usr/bin/objcopy /usr/bin/readelf /usr/bin/objdump /usr/bin/nm /usr/bin/shellcheck \
    /usr/bin/timeout /usr/bin/jq /usr/bin/bash /usr/bin/env /usr/bin/git /usr/bin/tar \
    /usr/bin/find /usr/bin/sort /usr/bin/xargs /usr/bin/sha256sum /usr/bin/stat \
    /usr/bin/od /usr/bin/cmp /usr/bin/cp /usr/bin/dd /usr/bin/head /usr/bin/grep \
    /usr/bin/awk /usr/bin/readlink /usr/bin/realpath "$compiler_frontend" \
    > "$output/metadata/tool-SHA256SUMS" 2> "$output/metadata/tool-hash.stderr"
end_phase

begin_phase build
# The package pins warningAsError. Audits below additionally set it explicitly.
checked lake build edsl-grade-call-memory-loop64 edsl-proof-export \
    tests.fixtures.CallMemoryLoop64.Audit \
    tests.fixtures.CallMemoryLoop64.ClosedForm.Audit \
    tests.fixtures.CallMemoryLoop64ClosedFormExports > "$output/build.log" 2>&1
end_phase

begin_phase audits
checked lake env lean -DwarningAsError=true tests/fixtures/CallMemoryLoop64/Audit.lean \
    > "$output/nested-audit.log" 2>&1
checked grep -Eq '^Audited [0-9]+ EDSL declarations; no unapproved axioms$' "$output/nested-audit.log"
checked lake env lean -DwarningAsError=true tests/fixtures/CallMemoryLoop64/ClosedForm/Audit.lean \
    > "$output/closed-form-audit.log" 2>&1
checked grep -Eq '^Audited [0-9]+ EDSL declarations; no unapproved axioms$' "$output/closed-form-audit.log"
cat > "$output/GradingEntries.lean" <<'LEAN'
import tests.fixtures.CallMemoryLoop64.Audit
import tests.fixtures.CallMemoryLoop64.ClosedForm.Audit
import tests.fixtures.CallMemoryLoop64ClosedFormExports
import EDSL.Grading.CallMemoryLoop64.Artifact
set_option warningAsError true
#check (EDSL.CallMemoryLoop64.GCC.claim :
  EDSL.CallMemoryLoop64.Claim (EDSL.CallMemoryLoop64.Compiler.program .gccSeparate))
#check (EDSL.CallMemoryLoop64.Clang.claim :
  EDSL.CallMemoryLoop64.Claim (EDSL.CallMemoryLoop64.Compiler.program .clangSeparate))
#check (EDSL.CallMemoryLoop64.ClosedForm.Exported.gcc :
  EDSL.CallMemoryLoop64.Claim (EDSL.CallMemoryLoop64.ClosedForm.program .gcc))
#check (EDSL.CallMemoryLoop64.ClosedForm.Exported.clang :
  EDSL.CallMemoryLoop64.Claim (EDSL.CallMemoryLoop64.ClosedForm.program .clang))
#print axioms EDSL.CallMemoryLoop64.ClosedForm.Exported.gcc
#print axioms EDSL.CallMemoryLoop64.ClosedForm.Exported.clang
#print axioms EDSL.Grading.CallMemoryLoop64.Artifact.certify
-- Accounting is a conclusion of the model execution, separate from Claim.
#check EDSL.CallMemoryLoop64.GCC.covered
#check EDSL.CallMemoryLoop64.Clang.covered
#print EDSL.CallMemoryLoop64.Clang.cost
#check EDSL.CallMemoryLoop64.ClosedForm.covered
#print EDSL.CallMemoryLoop64.ClosedForm.cost
#audit_edsl
LEAN
checked lake env lean -R "$output" -DwarningAsError=true "$output/GradingEntries.lean" > "$output/entry-and-accounting-audit.log" 2>&1
checked grep -Eq '^Audited [0-9]+ EDSL declarations; no unapproved axioms$' "$output/entry-and-accounting-audit.log"
end_phase

begin_phase installation
if installation_snapshot "$output/metadata/installation" > "$output/installation-snapshot.log" 2>&1; then
    installation_ready=true
else failure 'initial project/sysroot installation snapshot failed'; fi
end_phase

begin_phase nested-artifacts
printf 'profile\toriginal_raw\toriginal_elf\tentry\tspan\thelper\tcall\tcaller_ret\thelper_ret\n' > "$output/nested-inputs.tsv"
for index in 0 1; do
    profile=${profiles[index]}
    length=${lengths[index]}
    directory="$output/nested/$profile"
    mkdir -p "$directory"
    original=${inputs[index]}
    original_elf="$(run dirname -- "$original")/function.elf"
    checked realpath -e -- "$original" > "$directory/original-raw-path.txt" 2> "$directory/original-raw-path.stderr"
    if $command_ok; then original=$(< "$directory/original-raw-path.txt"); fi
    checked realpath -e -- "$original_elf" > "$directory/original-elf-path.txt" 2> "$directory/original-elf-path.stderr"
    if $command_ok; then original_elf=$(< "$directory/original-elf-path.txt"); fi
    printf '%s\t%s\t%s\t0\t%d\t%d\t%d\t%d\t%d\n' "$profile" "$original" "$original_elf" "$length" \
        "${helper_offsets[index]}" "${call_offsets[index]}" "${caller_rets[index]}" "${helper_rets[index]}" >> "$output/nested-inputs.tsv"
    remember_hashes "$directory/original-SHA256SUMS" "$original" "$original_elf"
    checked cp -- "$original" "$directory/text.bin" > "$directory/copy-raw.log" 2>&1
    checked cp -- "$original_elf" "$directory/function.elf" > "$directory/copy-elf.log" 2>&1
    checked cmp "$original" "$directory/text.bin" > "$directory/original-raw-binding.log" 2>&1
    checked cmp "$original_elf" "$directory/function.elf" > "$directory/original-elf-binding.log" 2>&1
    inspect_artifact "$directory" "$length"
    remember_hashes "$directory/artifact-SHA256SUMS" "$directory/text.bin" "$directory/function.elf"
done
end_phase

begin_phase closed-form-artifacts
# Exactly the parent's GNU23 -Os flags, with no closed-form tuning.
flags=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-stack-protector -fno-unwind-tables
    -fno-asynchronous-unwind-tables -fno-optimize-sibling-calls)
link_flags=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e caller -Ttext=0x401000)
{
    printf 'compiler_flags='; printf '%q ' "${flags[@]}"; printf '\n'
    printf 'linker_flags='; printf '%q ' "${link_flags[@]}"; printf '\n'
} > "$output/metadata/flags.txt"
printf '\110\215\004\026\110\205\322\164\007\110\215\120\377\110\211\027\303' > "$output/closed-form/gcc13-expected.bin"
printf '\110\211\360\110\001\320\110\205\322\164\007\110\215\110\377\110\211\017\303' > "$output/closed-form/clang18-expected.bin"
for index in 0 1; do
    compiler_name=${compiler_names[index]}
    if [[ $compiler_name == gcc13 ]]; then compiler=/usr/bin/gcc-13; else compiler=/usr/bin/clang-18; fi
    directory="$output/closed-form/$compiler_name"
    mkdir -p "$directory"
    checked "$compiler" "${flags[@]}" -c fixtures/call-memory-loop64-closed-form.c -o "$directory/function.o" \
        > "$directory/compile.log" 2>&1
    checked /usr/bin/ld "${link_flags[@]}" "$directory/function.o" -o "$directory/function.elf" \
        > "$directory/link.log" 2>&1
    checked /usr/bin/objcopy -O binary --only-section=.text "$directory/function.elf" "$directory/text.bin" \
        > "$directory/objcopy.log" 2>&1
    inspect_artifact "$directory" "${closed_lengths[index]}"
    checked cmp "$output/closed-form/$compiler_name-expected.bin" "$directory/text.bin" > "$directory/compiler-profile.log" 2>&1
    checked /usr/bin/objdump -drwC -Mintel --show-raw-insn "$directory/function.o" > "$directory/object-disassembly.txt" 2>&1
    checked /usr/bin/nm --defined-only "$directory/function.elf" > "$directory/symbols.txt" 2>&1
    remember_hashes "$directory/artifact-SHA256SUMS" "$directory/function.o" "$directory/function.elf" "$directory/text.bin"
done
end_phase

begin_phase nested-packets
for index in 0 1; do
    profile=${profiles[index]}
    packet="$output/packets/$profile.json"
    expect_case 0 "$export_pattern" "export-$profile" export \
        "${exporter[@]}" "${client_modules[index]}" "${client_claims[index]}" "$packet"
    if $case_ok; then
        if [[ -s $packet ]]; then
            packet_ready[index]=true
            remember_hashes "$packet.SHA256SUMS" "$packet"
        else failure "$profile exporter produced no packet"; fi
    fi
done
end_phase

begin_phase closed-form-packets
for index in 0 1; do
    compiler_name=${compiler_names[index]}
    packet="$output/packets/closed-form-$compiler_name.json"
    expect_case 0 "$export_pattern" "export-closed-form-$compiler_name" export \
        "${exporter[@]}" tests.fixtures.CallMemoryLoop64ClosedFormExports "${closed_claims[index]}" "$packet"
    if $case_ok; then
        if [[ -s $packet ]]; then
            closed_ready[index]=true
            remember_hashes "$packet.SHA256SUMS" "$packet"
        else failure "closed-form $compiler_name exporter produced no packet"; fi
    fi
done
end_phase

begin_phase nested-grades
for index in 0 1; do
    profile=${profiles[index]}
    directory="$output/nested/$profile"
    packet="$output/packets/$profile.json"
    length=${lengths[index]}
    if ! "${packet_ready[index]}"; then
        unavailable "$profile/raw" 'required nested packet unavailable'
        unavailable "$profile/elf" 'required nested packet unavailable'
        continue
    fi
    accept "$profile/raw" "$length" "${grader[@]}" 0 "$directory/text.bin" "$packet"
    if $case_ok; then nested_accepts=$((nested_accepts + 1)); fi
    accept "$profile/elf" "$length" "${grader[@]}" --elf "$length" 0 "$directory/function.elf" "$packet"
    if $case_ok; then nested_accepts=$((nested_accepts + 1)); fi
done
if [[ $nested_accepts != 4 ]]; then failure 'all four nested raw+ELF grades are required at default limits'; fi
end_phase

begin_phase closed-form-grades
for index in 0 1; do
    compiler_name=${compiler_names[index]}
    directory="$output/closed-form/$compiler_name"
    packet="$output/packets/closed-form-$compiler_name.json"
    length=${closed_lengths[index]}
    if ! "${closed_ready[index]}"; then
        unavailable "closed-form-$compiler_name/raw" 'required closed-form packet unavailable'
        unavailable "closed-form-$compiler_name/elf" 'required closed-form packet unavailable'
        continue
    fi
    accept "closed-form-$compiler_name/raw" "$length" "${grader[@]}" 0 "$directory/text.bin" "$packet"
    if $case_ok; then closed_form_accepts=$((closed_form_accepts + 1)); fi
    accept "closed-form-$compiler_name/elf" "$length" "${grader[@]}" --elf "$length" 0 "$directory/function.elf" "$packet"
    if $case_ok; then closed_form_accepts=$((closed_form_accepts + 1)); fi
done
if [[ $closed_form_accepts != 4 ]]; then failure 'all four fresh closed-form raw+ELF grades are required at default limits'; fi
end_phase

begin_phase protocol
foreign="$output/packets/foreign-write-v1.json"
# An actual trusted theorem for a legacy fixed task, not a made-up bad proof.
printf '%s\n' '["edsl-proof-v1",[],["const",["EDSL","Grading","Known","write"],[]]]' > "$foreign"
printf '\377' > "$output/negative/unsupported.bin"
printf '\377' > "$output/packets/invalid-utf8.json"
printf '%s\n' '["edsl-proof-v1",,[],[]]' > "$output/packets/invalid-json.json"
printf '%s\n' '["edsl-proof-unknown",[],[]]' > "$output/packets/invalid-version.json"
: > "$output/negative/empty.bin"
expect_case 2 "$usage" protocol/usage protocol-usage "${grader[@]}"
expect_case 2 "$usage" protocol/negative-entry protocol-usage "${grader[@]}" -1 "$output/negative/unsupported.bin" "$foreign"
expect_case 2 "$usage" protocol/nondecimal-span protocol-usage "${grader[@]}" --elf bad 0 "$output/negative/unsupported.bin" "$foreign"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: proof UTF-8; no defect conclusion' \
    protocol/proof-utf8 malformed "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/invalid-utf8.json"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: JSON syntax; no defect conclusion' \
    protocol/proof-json malformed "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/invalid-json.json"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: packet shape or version; no defect conclusion' \
    protocol/proof-version malformed "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/invalid-version.json"
checked dd if=/dev/zero of="$output/negative/oversized-raw.bin" bs=4097 count=1 status=none
checked dd if=/dev/zero of="$output/negative/oversized-elf.bin" bs=65537 count=1 status=none
checked dd if=/dev/zero of="$output/packets/oversized.json" bs=4194305 count=1 status=none
expect_case 6 "$resource" protocol/raw-byte-limit protocol-resource "${grader[@]}" 0 "$output/negative/oversized-raw.bin" "$foreign"
expect_case 6 "$resource" protocol/elf-byte-limit protocol-resource "${grader[@]}" --elf 45 0 "$output/negative/oversized-elf.bin" "$foreign"
expect_case 6 "$resource" protocol/proof-byte-limit protocol-resource "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/oversized.json"
# Check the other side of each I/O bound. These assert protocol boundaries,
# not semantic evidence about the zero-filled dummy candidate.
checked head -c 4096 "$output/negative/oversized-raw.bin" > "$output/negative/at-limit-raw.bin"
checked head -c 65536 "$output/negative/oversized-elf.bin" > "$output/negative/at-limit-elf.bin"
checked stat -c %s "$foreign" > "$output/packets/foreign-size.txt" 2>&1
foreign_size=$(< "$output/packets/foreign-size.txt")
if [[ $foreign_size =~ ^[0-9]+$ ]] && (( foreign_size < 4194304 )); then
    checked cp -- "$foreign" "$output/packets/at-limit.json"
    printf '%*s' "$((4194304 - foreign_size))" '' >> "$output/packets/at-limit.json"
    expect_case 5 "$rejected" protocol/proof-exact-byte-bound protocol-boundary \
        "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/at-limit.json"
else unavailable protocol/proof-exact-byte-bound 'could not size owned foreign packet'; fi
expect_case 5 "$rejected" protocol/raw-exact-byte-bound protocol-boundary "${grader[@]}" 0 "$output/negative/at-limit-raw.bin" "$foreign"
expect_case 3 "$unsupported" protocol/elf-exact-byte-bound protocol-boundary "${grader[@]}" --elf 45 0 "$output/negative/at-limit-elf.bin" "$foreign"
{
    for ((depth=0; depth<193; depth++)); do printf '['; done
    for ((depth=0; depth<193; depth++)); do printf ']'; done
    printf '\n'
} > "$output/packets/over-depth.json"
expect_case 6 'EDSLGrader.Runtime.FailureKind.resource: JSON depth; no defect conclusion' \
    protocol/json-depth protocol-resource "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/over-depth.json"
expect_case 1 "$internal" protocol/input-io protocol-io "${grader[@]}" 0 "$output/negative/nonexistent.bin" "$foreign"
expect_case 1 "$internal" protocol/proof-io protocol-io "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/nonexistent.json"
end_phase

begin_phase negatives
expect_case 5 "$rejected" negative/foreign-legacy-task semantic "${grader[@]}" 0 "$output/negative/unsupported.bin" "$foreign"
expect_case 3 "$unsupported" negative/empty-raw unsupported "${grader[@]}" 0 "$output/negative/empty.bin" "$foreign"
expect_case 3 "$unsupported" negative/raw-entry-out-of-bounds unsupported "${grader[@]}" 1 "$output/negative/unsupported.bin" "$foreign"
printf '\213' > "$output/negative/store-patch.bin"
printf '\100' > "$output/negative/prefix-patch.bin"
printf '\001\020\100\000\000\000\000\000' > "$output/negative/entry-patch.bin"
printf '\001\000\000\000\000\000\000\000' > "$output/negative/backing-patch.bin"
for index in 0 1; do
    profile=${profiles[index]}
    length=${lengths[index]}
    helper=${helper_offsets[index]}
    call_offset=${call_offsets[index]}
    original="$output/nested/$profile/text.bin"
    elf="$output/nested/$profile/function.elf"
    packet="$output/packets/$profile.json"
    if "${packet_ready[index]}"; then
        expect_case 5 "$rejected" "negative/$profile-wrong-entry" semantic "${grader[@]}" 1 "$original" "$packet"
        expect_case 5 "$rejected" "negative/$profile-helper-entry" semantic "${grader[@]}" "$helper" "$original" "$packet"
        next=$((1 - index))
        if "${packet_ready[next]}"; then
            expect_case 5 "$rejected" "negative/$profile-cross-profile" semantic \
                "${grader[@]}" 0 "$original" "$output/packets/${profiles[next]}.json"
        else unavailable "negative/$profile-cross-profile" 'required other nested packet unavailable'; fi
        for mutation in store helper-prefix omitted-helper truncated-call truncated-helper-ret extended; do
            mutant="$output/negative/$profile-$mutation.bin"
            case $mutation in
                store|helper-prefix)
                    checked cp -- "$original" "$mutant"
                    if [[ $mutation == store ]]; then patch=store; position=$((helper + 1))
                    else patch=prefix; position=$helper; fi
                    checked dd if="$output/negative/$patch-patch.bin" of="$mutant" bs=1 seek="$position" count=1 conv=notrunc status=none
                    ;;
                # Preserve the caller RET, omit the entire helper after it.
                omitted-helper) checked head -c "$helper" "$original" > "$mutant" ;;
                # Omit the last byte of the five-byte CALL at 20/24.
                truncated-call) checked head -c "$((call_offset + 4))" "$original" > "$mutant" ;;
                truncated-helper-ret) checked head -c "${helper_rets[index]}" "$original" > "$mutant" ;;
                extended) checked cp -- "$original" "$mutant"; printf '\220' >> "$mutant" ;;
            esac
            expect_case 5 "$rejected" "negative/$profile-$mutation" semantic "${grader[@]}" 0 "$mutant" "$packet"
        done
        changed_elf="$output/negative/$profile-store.elf"
        checked /usr/bin/objcopy --update-section ".text=$output/negative/$profile-store.bin" \
            "$elf" "$changed_elf" > "$changed_elf.objcopy.log" 2>&1
        expect_case 5 "$rejected" "negative/$profile-elf-selected-code" semantic "${grader[@]}" --elf "$length" 0 "$changed_elf" "$packet"
        expect_case 5 "$rejected" "negative/$profile-short-elf-span" semantic "${grader[@]}" --elf "$((length - 1))" 0 "$elf" "$packet"
    else unavailable "negative/$profile-proof-binding" 'required nested packet unavailable'; fi

    # Admission checks do not need a large client proof. Use the foreign packet
    # to ensure unsupported admission happens before proof type checking.
    expect_case 3 "$unsupported" "negative/$profile-raw-end-entry" unsupported "${grader[@]}" "$length" "$original" "$foreign"
    expect_case 3 "$unsupported" "negative/$profile-empty-elf" unsupported "${grader[@]}" --elf "$length" 0 "$output/negative/empty.bin" "$foreign"
    expect_case 3 "$unsupported" "negative/$profile-empty-elf-span" unsupported "${grader[@]}" --elf 0 0 "$elf" "$foreign"
    expect_case 3 "$unsupported" "negative/$profile-elf-entry-out-of-bounds" unsupported "${grader[@]}" --elf "$length" "$length" "$elf" "$foreign"
    expect_case 3 "$unsupported" "negative/$profile-elf-wrong-selected-entry" unsupported "${grader[@]}" --elf "$length" 1 "$elf" "$foreign"
    expect_case 3 "$unsupported" "negative/$profile-elf-overrun-span" unsupported "${grader[@]}" --elf "$((length + 1))" 0 "$elf" "$foreign"
    checked cp -- "$elf" "$output/negative/$profile-changed-entry.elf"
    # ELF64LE e_entry at byte24: 0x401000 -> 0x401001. The full 45/52-byte
    # window then overruns executable backing. Do not reuse the old span18.
    checked dd if="$output/negative/entry-patch.bin" of="$output/negative/$profile-changed-entry.elf" \
        bs=1 seek=24 count=8 conv=notrunc status=none
    checked /usr/bin/readelf -hW "$output/negative/$profile-changed-entry.elf" > "$output/negative/$profile-changed-entry.readelf.txt" 2>&1
    expect_case 3 "$unsupported" "negative/$profile-changed-elf-entry" unsupported "${grader[@]}" \
        --elf "$length" 0 "$output/negative/$profile-changed-entry.elf" "$foreign"

    # Locate the actual executable PT_LOAD instead of assuming its index.
    # All input integers are bounded to the owned <=64KiB ELF before arithmetic.
    program_offset=$(run od --endian=little -An -v -tu8 -j 32 -N 8 "$elf") || program_offset=
    program_count=$(run od --endian=little -An -v -tu2 -j 56 -N 2 "$elf") || program_count=
    program_size=$(run od --endian=little -An -v -tu2 -j 54 -N 2 "$elf") || program_size=
    executable_header=
    if [[ $program_offset =~ ^[[:space:]]*[0-9]{1,5}[[:space:]]*$ &&
          $program_count =~ ^[[:space:]]*[0-9]{1,2}[[:space:]]*$ &&
          $program_size =~ ^[[:space:]]*56[[:space:]]*$ ]] &&
        (( program_offset >= 64 && program_count > 0 && program_count <= 16 &&
           program_offset + program_count * 56 <= 65536 )); then
        for ((header_index=0; header_index<program_count; header_index++)); do
            base=$((program_offset + header_index * 56))
            kind=$(run od --endian=little -An -v -tu4 -j "$base" -N 4 "$elf") || kind=
            permissions=$(run od --endian=little -An -v -tu4 -j "$((base + 4))" -N 4 "$elf") || permissions=
            if [[ $kind =~ ^[[:space:]]*[0-9]{1,10}[[:space:]]*$ &&
                  $permissions =~ ^[[:space:]]*[0-9]{1,10}[[:space:]]*$ ]] &&
                (( kind == 1 && (permissions & 1) == 1 )); then executable_header=$base; break; fi
        done
    fi
    if [[ -n $executable_header ]]; then
        printf 'executable_program_header_file_offset=%d\n' "$executable_header" > "$output/negative/$profile-backing-binding.txt"
        checked cp -- "$elf" "$output/negative/$profile-unbacked-window.elf"
        # Entry remains backed; later selected bytes become BSS. p_filesz is +32.
        checked dd if="$output/negative/backing-patch.bin" of="$output/negative/$profile-unbacked-window.elf" \
            bs=1 seek="$((executable_header + 32))" count=8 conv=notrunc status=none
        checked /usr/bin/readelf -lW "$output/negative/$profile-unbacked-window.elf" > "$output/negative/$profile-unbacked-window.readelf.txt" 2>&1
        expect_case 3 "$unsupported" "negative/$profile-elf-unbacked-window" unsupported "${grader[@]}" \
            --elf "$length" 0 "$output/negative/$profile-unbacked-window.elf" "$foreign"
    else unavailable "negative/$profile-elf-unbacked-window" 'could not locate owned executable PT_LOAD'; fi
done

for index in 0 1; do
    compiler_name=${compiler_names[index]}
    length=${closed_lengths[index]}
    original="$output/closed-form/$compiler_name/text.bin"
    elf="$output/closed-form/$compiler_name/function.elf"
    packet="$output/packets/closed-form-$compiler_name.json"
    if ! "${closed_ready[index]}"; then
        unavailable "negative/closed-form-$compiler_name-binding" 'required closed-form packet unavailable'
        continue
    fi
    expect_case 5 "$rejected" "negative/closed-form-$compiler_name-wrong-entry" semantic "${grader[@]}" 1 "$original" "$packet"
    next=$((1 - index))
    if "${closed_ready[next]}"; then
        expect_case 5 "$rejected" "negative/closed-form-$compiler_name-cross-profile" semantic \
            "${grader[@]}" 0 "$original" "$output/packets/closed-form-${compiler_names[next]}.json"
    else unavailable "negative/closed-form-$compiler_name-cross-profile" 'required other closed-form packet unavailable'; fi
    if "${packet_ready[index]}"; then
        expect_case 5 "$rejected" "negative/closed-form-$compiler_name-nested-proof" semantic \
            "${grader[@]}" 0 "$original" "$output/packets/${profiles[index]}.json"
        expect_case 5 "$rejected" "negative/${profiles[index]}-closed-form-proof" semantic \
            "${grader[@]}" 0 "$output/nested/${profiles[index]}/text.bin" "$packet"
    else unavailable "negative/closed-form-$compiler_name-nested-proof" 'required nested packet unavailable'; fi
    for mutation in store truncated-ret extended; do
        mutant="$output/negative/closed-form-$compiler_name-$mutation.bin"
        case $mutation in
            store)
                checked cp -- "$original" "$mutant"
                checked dd if="$output/negative/store-patch.bin" of="$mutant" bs=1 \
                    seek="$((closed_stores[index] + 1))" count=1 conv=notrunc status=none
                ;;
            truncated-ret) checked head -c "$((length - 1))" "$original" > "$mutant" ;;
            extended) checked cp -- "$original" "$mutant"; printf '\220' >> "$mutant" ;;
        esac
        expect_case 5 "$rejected" "negative/closed-form-$compiler_name-$mutation" semantic "${grader[@]}" 0 "$mutant" "$packet"
    done
    changed_elf="$output/negative/closed-form-$compiler_name-store.elf"
    checked /usr/bin/objcopy --update-section ".text=$output/negative/closed-form-$compiler_name-store.bin" \
        "$elf" "$changed_elf" > "$changed_elf.objcopy.log" 2>&1
    expect_case 5 "$rejected" "negative/closed-form-$compiler_name-elf-selected-code" semantic \
        "${grader[@]}" --elf "$length" 0 "$changed_elf" "$packet"
    expect_case 5 "$rejected" "negative/closed-form-$compiler_name-short-elf-span" semantic \
        "${grader[@]}" --elf "$((length - 1))" 0 "$elf" "$packet"
done
end_phase

begin_phase container-reuse
printf 'Owned nonloaded grading note: a different ELF literal, the same selected program.\n' > "$output/metadata/container-note.txt"
for index in 0 1; do
    profile=${profiles[index]}
    length=${lengths[index]}
    directory="$output/nested/$profile/container-note"
    mkdir -p "$directory"
    checked /usr/bin/objcopy --add-section ".edsl_grading=$output/metadata/container-note.txt" \
        "$output/nested/$profile/function.elf" "$directory/function.elf" > "$directory/objcopy.log" 2>&1
    difference=0
    run cmp -s "$output/nested/$profile/function.elf" "$directory/function.elf" || difference=$?
    if [[ $difference != 1 ]]; then failure "$profile: container must differ with cmp exit1, observed=$difference"; fi
    checked cp -- "$output/nested/$profile/text.bin" "$directory/text.bin"
    inspect_artifact "$directory" "$length"
    remember_hashes "$directory/artifact-SHA256SUMS" "$directory/text.bin" "$directory/function.elf"
    if "${packet_ready[index]}"; then
        accept "container-reuse/$profile" "$length" "${grader[@]}" --elf "$length" 0 "$directory/function.elf" "$output/packets/$profile.json"
        if $case_ok; then container_accepts=$((container_accepts + 1)); fi
    else unavailable "container-reuse/$profile" 'required nested packet unavailable'; fi
done
if [[ $container_accepts != 2 ]]; then failure 'both legitimate nonloaded container changes must accept'; fi
end_phase

begin_phase isolation
poison="$output/poison"
for module in EDSL EDSL/Grading/Known EDSL/Grading/Artifact EDSL/Grading/CallStack/Artifact \
    EDSL/Grading/CallMemory64/Artifact EDSL/Grading/CallMemoryLoop64/Artifact \
    EDSL/Grading/AtomicLogical64/Artifact EDSL/Grading/AtomicSet64/Artifact \
    tests/fixtures/CallMemoryLoop64/GCC tests/fixtures/CallMemoryLoop64/Clang \
    tests/fixtures/CallMemoryLoop64/ClosedForm tests/fixtures/CallMemoryLoop64ClosedFormExports; do
    mkdir -p "$poison/${module%/*}"
    for suffix in olean olean.private olean.server so; do
        printf 'Untrusted LEAN_PATH sentinel; deliberately not a Lean object\n' > "$poison/$module.$suffix"
    done
done
all_claims=("${client_claims[@]}" "${closed_claims[@]}")
for client_index in 0 1 2 3; do
    index=$((client_index % 2))
    if (( client_index < 2 )); then
        name=${profiles[index]}
        directory="$output/nested/$name"
        length=${lengths[index]}
        packet="$output/packets/$name.json"
        ready=${packet_ready[index]}
    else
        name="closed-form-${compiler_names[index]}"
        directory="$output/closed-form/${compiler_names[index]}"
        length=${closed_lengths[index]}
        packet="$output/packets/$name.json"
        ready=${closed_ready[index]}
    fi
    reference="$output/packets/$name-reference-only-v1.json"
    # Only this synthetic reference packet is constructed here. Actual exports
    # are used unchanged; no rewriting packets or injecting trusted declarations.
    # shellcheck disable=SC2016
    checked jq -nc --arg name "${all_claims[client_index]}" \
        '["edsl-proof-v1",[],["const",($name|split(".")),[]]]' > "$reference" 2> "$reference.stderr"
    expect_case 4 "$unknown" "isolation/$name-reference-only" isolation "${grader[@]}" 0 "$directory/text.bin" "$reference"
    if $case_ok; then reference_rejections=$((reference_rejections + 1)); fi
    expect_case 4 "$unknown" "isolation/$name-poisoned-reference-only" isolation \
        lake env env LEAN_PATH="$poison" .lake/build/bin/edsl-grade-call-memory-loop64 0 "$directory/text.bin" "$reference"
    if $case_ok; then reference_rejections=$((reference_rejections + 1)); fi
    if "$ready"; then
        accept "isolation/$name-poisoned-raw" "$length" lake env env LEAN_PATH="$poison" \
            .lake/build/bin/edsl-grade-call-memory-loop64 0 "$directory/text.bin" "$packet"
        if $case_ok; then poisoned_accepts=$((poisoned_accepts + 1)); fi
        accept "isolation/$name-poisoned-elf" "$length" lake env env LEAN_PATH="$poison" \
            .lake/build/bin/edsl-grade-call-memory-loop64 --elf "$length" 0 "$directory/function.elf" "$packet"
        if $case_ok; then poisoned_accepts=$((poisoned_accepts + 1)); fi
    else unavailable "isolation/$name-poisoned-packet" 'required serialized packet unavailable'; fi
done
if (( reference_rejections != 8 || poisoned_accepts != 8 )); then failure 'all four plain/poisoned references and poisoned raw+ELF packets are required'; fi
end_phase

begin_phase source-stability
if public_snapshot "$output/public-source-final" > "$output/source-final-snapshot.log" 2>&1; then
    if $source_ready; then
        checked cmp "$output/public-source.files.list0" "$output/public-source-final.files.list0" > "$output/source-list-stability.log" 2>&1
        checked cmp "$output/public-source.tar" "$output/public-source-final.tar" > "$output/source-stability.log" 2>&1
        checked sha256sum -c "$output/public-source.file-SHA256SUMS" > "$output/source-hash-stability.log" 2>&1
    else failure 'initial public source snapshot unavailable'; fi
else failure 'final public source snapshot failed'; fi
checked git rev-parse HEAD > "$output/metadata/final-HEAD.txt" 2>&1
checked cmp "$output/metadata/HEAD.txt" "$output/metadata/final-HEAD.txt" > "$output/head-stability.log" 2>&1
end_phase

begin_phase input-stability
# 2 original pairs + 2 copied pairs + 2 closed-form triples + 4 exported
# packets + 2 alternate containers = twelve distinct mandatory receipts.
if (( ${#required_receipts[@]} != 12 || ${#stability_receipts[@]} != 12 )); then
    failure 'not all twelve required input/packet/container hash receipts were captured'
fi
for receipt in "${required_receipts[@]}"; do
    if [[ ${receipt_seen[$receipt]:-false} != true || ! -s $receipt ]]; then
        failure "required hash receipt missing: $receipt"
        continue
    fi
    checked sha256sum -c "$receipt" > "$receipt.stability.log" 2>&1
done
end_phase

begin_phase installation-stability
if installation_snapshot "$output/metadata/installation-final" > "$output/installation-final-snapshot.log" 2>&1; then
    if $installation_ready; then
        checked cmp "$output/metadata/installation.files.list0" "$output/metadata/installation-final.files.list0" \
            > "$output/installation-list-stability.log" 2>&1
        checked cmp "$output/metadata/installation.SHA256SUMS" "$output/metadata/installation-final.SHA256SUMS" \
            > "$output/installation-stability.log" 2>&1
        checked cmp "$output/metadata/installation.metadata.txt" "$output/metadata/installation-final.metadata.txt" \
            > "$output/installation-metadata-stability.log" 2>&1
    else failure 'initial installation snapshot unavailable'; fi
else failure 'final installation snapshot failed'; fi
checked sha256sum -c "$output/metadata/tool-SHA256SUMS" > "$output/tool-stability.log" 2>&1
end_phase

begin_phase evidence-closure
# Use builtins for the last ledger check: no pending logged command can be
# omitted from the command/status bijection we are validating.
validate_ledgers() {
    local line tag logged_phase status extra name category expected observed result diagnostic
    local command_count=0 status_count=0 case_count=0
    local -A commands_seen=() statuses_seen=() cases_seen=()
    while IFS= read -r line; do
        if [[ ! $line =~ ^\[([0-9]+\.[0-9]+)\]\ phase=([a-z-]+)\ cwd= ]]; then
            failure 'malformed command ledger record'
            continue
        fi
        tag=${BASH_REMATCH[1]}
        logged_phase=${BASH_REMATCH[2]}
        if [[ -n ${commands_seen[$tag]:-} ]]; then failure "duplicate command tag: $tag"; fi
        commands_seen[$tag]=$logged_phase
        command_count=$((command_count + 1))
    done < "$output/commands.log"
    {
        IFS= read -r line
        if [[ $line != $'tag\tphase\texit' ]]; then failure 'bad command-status header'; fi
        while IFS=$'\t' read -r tag logged_phase status extra; do
            if [[ ! $tag =~ ^[0-9]+\.[0-9]+$ || ! $status =~ ^[0-9]{1,3}$ || -n $extra ]]; then
                failure 'malformed command-status record'
                continue
            fi
            if (( status > 255 )) || [[ ${commands_seen[$tag]:-} != "$logged_phase" ||
                ${statuses_seen[$tag]:-false} == true ]]; then
                failure "unmatched/duplicate command status: $tag"
            fi
            statuses_seen[$tag]=true
            status_count=$((status_count + 1))
        done
    } < "$output/command-status.tsv"
    for tag in "${!commands_seen[@]}"; do
        if [[ ${statuses_seen[$tag]:-false} != true ]]; then failure "command has no completed status: $tag"; fi
    done
    if (( command_count == 0 || command_count != status_count )); then failure 'command/status ledger is incomplete'; fi
    {
        IFS= read -r line
        if [[ $line != $'case\tcategory\texpected\tobserved\tresult\tdiagnostic' ]]; then failure 'bad case-status header'; fi
        while IFS=$'\t' read -r name category expected observed result diagnostic; do
            if [[ -z $name || -n ${cases_seen[$name]:-} ]]; then
                failure 'empty or duplicate case name'
                continue
            fi
            cases_seen[$name]=true
            case_count=$((case_count + 1))
            if [[ ! $expected =~ ^[0-6]$ || $expected != "$observed" || $result != PASS ||
                  -z $category || -z $diagnostic || ! -f $output/cases/$name/exit-status.txt ||
                  ! -f $output/cases/$name/stdout.txt || ! -f $output/cases/$name/stderr.txt ]]; then
                failure "case did not complete as specified: $name"
            elif [[ $(< "$output/cases/$name/exit-status.txt") != "$observed" ]]; then
                failure "case status receipt mismatch: $name"
            fi
        done
    } < "$output/case-status.tsv"
    # 4 exports + 8 primary grades + 15 protocol + 59 binding/admission
    # negatives + 2 container accepts + 16 isolation cases.
    if (( case_count != 104 )); then failure "required matrix incomplete: $case_count/104 cases"; fi
    printf 'completed_commands=%d completed_statuses=%d completed_cases=%d required_cases=104\n' \
        "$command_count" "$status_count" "$case_count" > "$output/ledger-closure.txt"
}
validate_ledgers
end_phase
suite_complete=true
if [[ $failures != 0 ]]; then exit 1; fi
