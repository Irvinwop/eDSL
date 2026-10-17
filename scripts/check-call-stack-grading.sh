#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# The caller holds /tmp/edsl-lean-build.lock for this entire script. Do not
# acquire that lock again here: verify-call-stack.sh calls us under flock.
set -euo pipefail
umask 022
if [[ $# != 5 ]]; then
    echo 'usage: scripts/check-call-stack-grading.sh OUTPUT GCC_SAME_BIN GCC_SEP_BIN CLANG_SAME_BIN CLANG_SEP_BIN' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=$1
shift
mkdir -p -- "$output"
output=$(cd "$output" && pwd)
# Refuse to mix a new run with old packets or an old PASS result.
existing=$(find "$output" -mindepth 1 -maxdepth 1 -print -quit)
if [[ -n $existing ]]; then
    echo 'Call-stack grading requires an empty OUTPUT directory' >&2
    exit 2
fi
export LEAN_NUM_THREADS=1
inputs=("$@")
profiles=(gccSame gccSeparate clangSame clangSeparate)
entries=(5 0 5 0)
lengths=(14 16 16 16)
phases=(sources script-checks tools build accounting compiler-artifacts
    compiler-packets compiler-grades inline-artifacts inline-packet
    inline-grades negatives isolation source-stability)
declare -A phase_status
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
phase=setup
sequence=0
failures=0
phase_start_failures=0
suite_complete=false
case_ok=false
compiler_accepts=0
inline_accepts=0
packet_ready=(false false false false)
inline_ready=false
exec 3>"$output/commands.log" 4>"$output/command-status.tsv" 5>"$output/case-status.tsv"
printf 'sequence\tphase\texit\n' >&4
printf 'case\texpected\tobserved\tresult\treason\n' >&5

run() {
    sequence=$((sequence + 1))
    printf '%06d\t%s\tcwd=%q\targv=' "$sequence" "$phase" "$PWD" >&3
    printf '%q ' "$@" >&3
    printf '\n' >&3
    local status=0
    "$@" || status=$?
    printf '%06d\t%s\t%d\n' "$sequence" "$phase" "$status" >&4
    return "$status"
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
}
end_phase() {
    if [[ $failures == "$phase_start_failures" ]]; then
        phase_status[$phase]=PASS
    else
        phase_status[$phase]=FAIL
    fi
    write_phases
}
failure() {
    failures=$((failures + 1))
    printf 'Call-stack grading: %s (see %s)\n' "$1" "$output" >&2
}
manifest() {
    (
        cd "$output" || exit 1
        # Check enumeration before reading the NUL-delimited list. Process
        # substitution would hide failures in find/sort from set -e.
        # find only compares the excluded list's name; it never reads it.
        # shellcheck disable=SC2094
        find . -type f ! -name SHA256SUMS ! -name MANIFEST-SHA256.txt \
            ! -name manifest-inputs.list0 -print0 | sort -z > manifest-inputs.list0 || exit 1
        local -a files
        mapfile -d '' -t files < manifest-inputs.list0 || exit 1
        [[ ${#files[@]} -gt 0 ]] || exit 1
        sha256sum -- manifest-inputs.list0 "${files[@]}" > SHA256SUMS || exit 1
        sha256sum SHA256SUMS > MANIFEST-SHA256.txt || exit 1
    )
}
finish() {
    local status=$? name result=FAIL
    trap - EXIT
    if [[ ${phase_status[$phase]:-NOTRUN} == RUNNING ]]; then phase_status[$phase]=FAIL; fi
    if [[ $status == 0 ]] && $suite_complete && [[ $failures == 0 ]]; then
        result=PASS
        for name in "${phases[@]}"; do
            if [[ ${phase_status[$name]} != PASS ]]; then result=FAIL; fi
        done
    fi
    if [[ $result != PASS ]]; then status=1; fi
    write_phases
    printf 'grading=%s compiler_raw_elf=%d/8 inline_raw_elf=%d/4 native_inline=NOTRUN failures=%d\n' \
        "$result" "$compiler_accepts" "$inline_accepts" "$failures" > "$output/result.txt"
    printf 'exit=%d UTC=%s final_phase=%s complete=%s\n' \
        "$status" "$(date -u +%FT%TZ)" "$phase" "$suite_complete" > "$output/terminal-status.txt"
    exec 3>&- 4>&- 5>&-
    if ! manifest; then
        status=1
        printf 'grading=FAIL reason=evidence_manifest\n' > "$output/result.txt"
        printf 'exit=1 reason=evidence_manifest\n' > "$output/terminal-status.txt"
    fi
    printf 'Call-stack grading: %s; evidence=%s\n' "$(cat "$output/result.txt")" "$output" >&2
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Every CLI/export case keeps separate, complete output. Exact status and
# diagnostic checks exclude timeouts, signals, IO failures and resource limits
# from the semantic negatives. Export failures remain failures, never skips
# promoted to success; independent phases still run to completion.
expect_case() {
    local expected=$1 reason=$2 name=$3 status=0 result=FAIL
    shift 3
    local directory="$output/cases/$name"
    mkdir -p -- "$directory"
    run timeout --signal=TERM --kill-after=5s 60s "$@" \
        > "$directory/stdout.txt" 2> "$directory/stderr.txt" || status=$?
    case_ok=false
    if [[ $status == "$expected" ]]; then
        if [[ $expected == 0 ]]; then
            if [[ ! -s $directory/stderr.txt ]] && grep -Eq "$reason" "$directory/stdout.txt" &&
                [[ $(wc -l < "$directory/stdout.txt") == 1 ]]; then case_ok=true; fi
        elif [[ ! -s $directory/stdout.txt ]] &&
            grep -Fxq "$reason" "$directory/stderr.txt" &&
            [[ $(wc -l < "$directory/stderr.txt") == 1 ]]; then
            case_ok=true
        fi
    fi
    if $case_ok; then result=PASS; else failure "$name expected=$expected observed=$status"; fi
    printf '%s\t%d\t%d\t%s\t%s\n' "$name" "$expected" "$status" "$result" "$reason" >&5
}
skip_case() {
    printf '%s\t-\tNOTRUN\tFAIL\t%s\n' "$1" "$2" >&5
    failure "$1: $2"
}
accept() {
    local name=$1 length=$2
    shift 2
    expect_case 0 "^ACCEPTED: fixed call contract, exact artifact, selected entry and current OS resources; codeBytes=$length, " \
        "$name" "$@"
}
rejected='EDSLGrader.Runtime.FailureKind.rejected: kernel declTypeMismatch; no defect conclusion'
unsupported='EDSLGrader.Runtime.FailureKind.unsupported: call artifact admission failed; no defect conclusion'
unknown='EDSLGrader.Runtime.FailureKind.malformed: unknown constant; no defect conclusion'
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade-call-stack)

begin_phase sources
mkdir -p "$output/metadata" "$output/compiler" "$output/inline" "$output/packets" "$output/negative"
# Include dirty and untracked public source files, not merely HEAD. Ignored
# private storage and build/evidence directories are outside this snapshot.
snapshot_exclusions=()
if [[ $output == "$PWD/"* ]]; then snapshot_exclusions=(":(top,exclude)${output#"$PWD/"}"); fi
run git ls-files --cached --others --exclude-standard -z -- . "${snapshot_exclusions[@]}" \
    > "$output/source-inputs.unsorted.list0"
run sort -zu "$output/source-inputs.unsorted.list0" > "$output/source-inputs.list0"
mapfile -d '' -t source_files < "$output/source-inputs.list0"
[[ ${#source_files[@]} -gt 0 ]]
run sha256sum -- "${source_files[@]}" > "$output/source-SHA256SUMS"
run tar -czf "$output/source-snapshot.tar.gz" -- "${source_files[@]}"
run sha256sum -c "$output/source-SHA256SUMS" > "$output/snapshot-stability.log" 2>&1
run git rev-parse HEAD > "$output/metadata/HEAD.txt"
run git status --short --branch > "$output/metadata/worktree.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned synthetic compiler artifacts only. The four previously authenticated
nested-call inputs are copied together with their complete sibling ELFs, then
independently graded against the fixed resource-first call contract. Every
raw file, entry offset, complete ELF file and selected whole-window span is
bound by the actual CLI's kernel-checked artifact theorem. Helpers before the
entry and code after the first RET remain in the selected window.

The same independently exported Inline.claim packet must accept both actual
GCC13 and Clang18 five-byte whole texts and both complete ELFs. These are
proof-only compiler artifact grades. This script executes no raw inputs and
performs no native inline observations. The parent native runner observes four
nested-call profiles. Inline exact_two and optimal_for_useful_inputs are built
and audited separately through Inline.Accounting; instruction counts and read
order are not acceptance criteria. No compiler-preservation or native CPU
correspondence is established here. Environmental assumptions are those of
the fixed Lean contract and the trusted pinned Lean/CLI installation.

Only the client exporter imports sourceModule. The grader receives packet
data, never a candidate Lean module or an import/search-path request. Reference
packets without declarations must not find the built client constants. Poisoned
LEAN_PATH tests use corrupt object-file sentinels, not installed candidate
modules. Default verifier/exporter limits are unchanged. Rejection, unsupported
input, proof failure and resource exhaustion establish no security defect.
Any missing packet, incomplete phase, timeout, signal or unexpected diagnostic
fails the suite. Complete per-case stdout/stderr, sources, packets, compiler
objects, exact raw/ELF inputs and command statuses are retained in this run.
SCOPE
end_phase

begin_phase script-checks
run bash -n scripts/check-call-stack-grading.sh > "$output/bash-n.log" 2>&1
run shellcheck -s bash scripts/check-call-stack-grading.sh > "$output/shellcheck.log" 2>&1
end_phase

begin_phase tools
{
    run date -u +%FT%TZ
    run uname -a
    run lake --version
    run /usr/bin/gcc-13 --version
    run /usr/bin/gcc-13 -dumpmachine
    run /usr/bin/clang-18 --version
    run /usr/bin/clang-18 -print-target-triple
    run /usr/bin/ld --version
    run /usr/bin/objcopy --version
    run /usr/bin/readelf --version
    run /usr/bin/objdump --version
    run shellcheck --version
} > "$output/metadata/tools.txt" 2>&1
run sha256sum /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as \
    /usr/bin/objcopy /usr/bin/readelf /usr/bin/objdump > "$output/metadata/tool-SHA256SUMS"
end_phase

begin_phase build
run lake build edsl-grade-call-stack edsl-proof-export tests.fixtures.CallStack.Covered \
    > "$output/build.log" 2>&1
run sha256sum .lake/build/bin/edsl-grade-call-stack .lake/build/bin/edsl-proof-export \
    > "$output/metadata/grader-exporter-SHA256SUMS"
end_phase

begin_phase accounting
run lake build tests.fixtures.CallStack.Inline.Accounting > "$output/accounting-build.log" 2>&1
end_phase

begin_phase compiler-artifacts
printf 'profile\toriginal_raw\toriginal_elf\tentry\tspan\n' > "$output/compiler-inputs.tsv"
for index in 0 1 2 3; do
    directory="$output/compiler/${profiles[index]}"
    mkdir -p "$directory"
    original=${inputs[index]}
    original_elf="$(dirname "$original")/function.elf"
    printf '%s\t%s\t%s\t%d\t%d\n' "${profiles[index]}" "$original" "$original_elf" \
        "${entries[index]}" "${lengths[index]}" >> "$output/compiler-inputs.tsv"
    run cp -- "$original" "$directory/text.bin"
    run cp -- "$original_elf" "$directory/function.elf"
    run stat -c %s -- "$directory/text.bin" > "$directory/span.txt"
    read -r length < "$directory/span.txt"
    [[ $length == "${lengths[index]}" ]]
    run /usr/bin/objcopy -O binary --only-section=.text "$directory/function.elf" "$directory/extracted-text.bin"
    run cmp "$directory/text.bin" "$directory/extracted-text.bin"
    run /usr/bin/readelf -aW "$directory/function.elf" > "$directory/readelf.txt"
    run /usr/bin/objdump -drwC -Mintel --show-raw-insn "$directory/function.elf" > "$directory/disassembly.txt"
    run sha256sum "$directory/text.bin" "$directory/function.elf" > "$directory/artifact-SHA256SUMS"
done
end_phase

begin_phase compiler-packets
for index in 0 1 2 3; do
    profile=${profiles[index]}
    packet="$output/packets/$profile.json"
    expect_case 0 '^EXPORTED: client packet; auxiliaryDeclarations=[1-9][0-9]*, ' "export-$profile" \
        "${exporter[@]}" tests.fixtures.CallStack.Covered "EDSL.CallStack.Client.$profile" "$packet"
    if $case_ok; then
        if [[ -s $packet ]]; then packet_ready[index]=true; else failure "$profile export produced no packet"; fi
    fi
done
end_phase

begin_phase compiler-grades
for index in 0 1 2 3; do
    profile=${profiles[index]}
    directory="$output/compiler/$profile"
    packet="$output/packets/$profile.json"
    if ! "${packet_ready[index]}"; then
        skip_case "$profile/raw" 'required compiler packet unavailable'
        skip_case "$profile/elf" 'required compiler packet unavailable'
        continue
    fi
    accept "$profile/raw" "${lengths[index]}" "${grader[@]}" "${entries[index]}" "$directory/text.bin" "$packet"
    if $case_ok; then compiler_accepts=$((compiler_accepts + 1)); fi
    accept "$profile/elf" "${lengths[index]}" "${grader[@]}" --elf "${lengths[index]}" \
        "${entries[index]}" "$directory/function.elf" "$packet"
    if $case_ok; then compiler_accepts=$((compiler_accepts + 1)); fi
done
if [[ $compiler_accepts != 8 ]]; then failure 'all four compiler raw+ELF grades are required'; fi
end_phase

begin_phase inline-artifacts
# Exactly the original nested-call compile/link flags, including disabled
# sibling-call optimization. No option tuning to obtain the five-byte result.
flags=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-stack-protector -fno-unwind-tables
    -fno-asynchronous-unwind-tables -fno-optimize-sibling-calls)
link_flags=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e caller -Ttext=0x401000)
for compiler_name in gcc13 clang18; do
    if [[ $compiler_name == gcc13 ]]; then compiler=/usr/bin/gcc-13; else compiler=/usr/bin/clang-18; fi
    directory="$output/inline/$compiler_name"
    mkdir -p "$directory"
    run "$compiler" "${flags[@]}" -c fixtures/call-stack-inline.c -o "$directory/function.o" \
        > "$directory/compile.log" 2>&1
    run /usr/bin/ld "${link_flags[@]}" "$directory/function.o" -o "$directory/function.elf" \
        > "$directory/link.log" 2>&1
    run /usr/bin/objcopy -O binary --only-section=.text "$directory/function.elf" "$directory/text.bin"
    run stat -c %s -- "$directory/text.bin" > "$directory/span.txt"
    read -r length < "$directory/span.txt"
    [[ $length == 5 ]]
    run /usr/bin/readelf -aW "$directory/function.elf" > "$directory/readelf.txt"
    run /usr/bin/readelf -rW "$directory/function.elf" > "$directory/relocations.txt"
    run grep -Fxq 'There are no relocations in this file.' "$directory/relocations.txt"
    run /usr/bin/objdump -drwC -Mintel --show-raw-insn "$directory/function.o" > "$directory/object-disassembly.txt"
    run /usr/bin/objdump -drwC -Mintel --show-raw-insn "$directory/function.elf" > "$directory/disassembly.txt"
    run sha256sum "$directory/function.o" "$directory/function.elf" "$directory/text.bin" > "$directory/artifact-SHA256SUMS"
done
end_phase

begin_phase inline-packet
inline_packet="$output/packets/inline.json"
expect_case 0 '^EXPORTED: client packet; auxiliaryDeclarations=[1-9][0-9]*, ' export-inline \
    "${exporter[@]}" tests.fixtures.CallStack.Inline EDSL.CallStack.Inline.claim "$inline_packet"
if $case_ok; then
    if [[ -s $inline_packet ]]; then inline_ready=true; else failure 'inline export produced no packet'; fi
fi
end_phase

begin_phase inline-grades
for compiler_name in gcc13 clang18; do
    directory="$output/inline/$compiler_name"
    if ! $inline_ready; then
        skip_case "inline-$compiler_name/raw" 'required inline packet unavailable'
        skip_case "inline-$compiler_name/elf" 'required inline packet unavailable'
        continue
    fi
    accept "inline-$compiler_name/raw" 5 "${grader[@]}" 0 "$directory/text.bin" "$inline_packet"
    if $case_ok; then inline_accepts=$((inline_accepts + 1)); fi
    accept "inline-$compiler_name/elf" 5 "${grader[@]}" --elf 5 0 "$directory/function.elf" "$inline_packet"
    if $case_ok; then inline_accepts=$((inline_accepts + 1)); fi
done
if [[ $inline_accepts != 4 ]]; then failure 'both inline compiler raw+ELF grades are required'; fi
end_phase

begin_phase negatives
# The existing trusted write theorem is EDSL.Grading.Known.write. A real
# fixed-task theorem, rather than True or an unknown name, tests engine binding.
foreign="$output/packets/foreign-write-v1.json"
printf '%s\n' '["edsl-proof-v1",[],["const",["EDSL","Grading","Known","write"],[]]]' > "$foreign"
printf '\377' > "$output/negative/unsupported.bin"
printf '\377' > "$output/packets/invalid-utf8.json"
printf '%s\n' '["edsl-proof-v1",,[],[]]' > "$output/packets/invalid-json.json"
: > "$output/negative/empty.bin"
inline_raw="$output/inline/gcc13/text.bin"
inline_elf="$output/inline/gcc13/function.elf"
expect_case 5 "$rejected" negative/foreign-legacy-task "${grader[@]}" 0 "$inline_raw" "$foreign"
expect_case 5 "$rejected" negative/unsupported-wrong-engine "${grader[@]}" 0 "$output/negative/unsupported.bin" "$foreign"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: proof UTF-8; no defect conclusion' \
    negative/proof-utf8 "${grader[@]}" 0 "$inline_raw" "$output/packets/invalid-utf8.json"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: JSON syntax; no defect conclusion' \
    negative/proof-json "${grader[@]}" 0 "$inline_raw" "$output/packets/invalid-json.json"
expect_case 3 "$unsupported" negative/empty-raw "${grader[@]}" 0 "$output/negative/empty.bin" "$foreign"
expect_case 3 "$unsupported" negative/raw-entry-out-of-bounds "${grader[@]}" 5 "$inline_raw" "$foreign"
expect_case 3 "$unsupported" negative/empty-elf-span "${grader[@]}" --elf 0 0 "$inline_elf" "$foreign"
expect_case 3 "$unsupported" negative/elf-entry-out-of-bounds "${grader[@]}" --elf 5 5 "$inline_elf" "$foreign"
expect_case 3 "$unsupported" negative/elf-overrun-span "${grader[@]}" --elf 4096 0 "$inline_elf" "$foreign"
run cp "$inline_elf" "$output/negative/changed-entry.elf"
# ELF64 little-endian e_entry at byte 24: 0x401000 -> 0x401001.
printf '\001\020\100\000\000\000\000\000' > "$output/negative/entry-patch.bin"
run dd if="$output/negative/entry-patch.bin" of="$output/negative/changed-entry.elf" \
    bs=1 seek=24 count=8 conv=notrunc status=none
run /usr/bin/readelf -hW "$output/negative/changed-entry.elf" > "$output/negative/changed-entry.readelf.txt"
expect_case 3 "$unsupported" negative/changed-elf-entry "${grader[@]}" --elf 5 0 "$output/negative/changed-entry.elf" "$foreign"
if $inline_ready; then
    expect_case 5 "$rejected" negative/inline-wrong-entry "${grader[@]}" 1 "$inline_raw" "$inline_packet"
    run cp "$inline_raw" "$output/negative/inline-appended.bin"
    printf '\220' >> "$output/negative/inline-appended.bin"
    expect_case 5 "$rejected" negative/inline-appended-byte "${grader[@]}" \
        0 "$output/negative/inline-appended.bin" "$inline_packet"
else
    skip_case negative/inline-proof-binding 'required inline packet unavailable'
fi
printf '\002' > "$output/negative/helper-patch.bin"
for index in 0 1 2 3; do
    profile=${profiles[index]}
    packet="$output/packets/$profile.json"
    original="$output/compiler/$profile/text.bin"
    if ! "${packet_ready[index]}"; then
        skip_case "negative/$profile-proof-binding" 'required compiler packet unavailable'
        continue
    fi
    if [[ ${entries[index]} == 0 ]]; then wrong_entry=1; else wrong_entry=0; fi
    expect_case 5 "$rejected" "negative/$profile-wrong-entry" "${grader[@]}" "$wrong_entry" "$original" "$packet"
    next=$(((index + 1) % 4))
    if "${packet_ready[next]}"; then
        expect_case 5 "$rejected" "negative/$profile-cross-profile" "${grader[@]}" \
            "${entries[index]}" "$original" "$output/packets/${profiles[next]}.json"
    else
        skip_case "negative/$profile-cross-profile" 'required other-profile packet unavailable'
    fi
    run cp "$original" "$output/negative/$profile-appended.bin"
    printf '\220' >> "$output/negative/$profile-appended.bin"
    expect_case 5 "$rejected" "negative/$profile-appended-byte" "${grader[@]}" \
        "${entries[index]}" "$output/negative/$profile-appended.bin" "$packet"
    if [[ ${entries[index]} == 5 ]]; then
        run cp "$original" "$output/negative/$profile-helper-changed.bin"
        # Mutate the helper's LEA immediate before entry, preserving its RET.
        run dd if="$output/negative/helper-patch.bin" of="$output/negative/$profile-helper-changed.bin" \
            bs=1 seek=3 count=1 conv=notrunc status=none
        expect_case 5 "$rejected" "negative/$profile-helper-prefix-changed" "${grader[@]}" \
            5 "$output/negative/$profile-helper-changed.bin" "$packet"
        run tail -c +6 "$original" > "$output/negative/$profile-helper-omitted.bin"
        expect_case 5 "$rejected" "negative/$profile-helper-prefix-omitted" "${grader[@]}" \
            0 "$output/negative/$profile-helper-omitted.bin" "$packet"
    fi
done
if "${packet_ready[0]}"; then
    original="$output/compiler/gccSame/text.bin"
    packet="$output/packets/gccSame.json"
    # CALL starts at offset 5; a 9-byte file clips its four-byte immediate.
    run head -c 9 "$original" > "$output/negative/call-immediate-clipped.bin"
    expect_case 5 "$rejected" negative/truncated-call-immediate "${grader[@]}" \
        5 "$output/negative/call-immediate-clipped.bin" "$packet"
    run head -c 5 "$original" > "$output/negative/helper-first-ret.bin"
    expect_case 3 "$unsupported" negative/first-ret-before-entry "${grader[@]}" \
        5 "$output/negative/helper-first-ret.bin" "$packet"
else
    skip_case negative/truncated-call-immediate 'required gccSame packet unavailable'
    skip_case negative/first-ret-before-entry 'required gccSame packet unavailable'
fi
if "${packet_ready[1]}"; then
    # The separate-TU caller RET precedes its helper. An entry-forward
    # first-RET scan would incorrectly omit the actual callee from this file.
    run head -c 11 "$output/compiler/gccSeparate/text.bin" > "$output/negative/caller-first-ret.bin"
    expect_case 5 "$rejected" negative/first-ret-omits-helper "${grader[@]}" \
        0 "$output/negative/caller-first-ret.bin" "$output/packets/gccSeparate.json"
else
    skip_case negative/first-ret-omits-helper 'required gccSeparate packet unavailable'
fi
end_phase

begin_phase isolation
reference="$output/packets/client-reference-only-v1.json"
printf '%s\n' '["edsl-proof-v1",[],["const",["EDSL","CallStack","Client","gccSame"],[]]]' > "$reference"
expect_case 4 "$unknown" isolation/client-reference-only "${grader[@]}" \
    5 "$output/compiler/gccSame/text.bin" "$reference"
poison="$output/poison"
mkdir -p "$poison/EDSL/Grading/CallStack" "$poison/tests/fixtures/CallStack"
for module in EDSL/Grading/Known EDSL/Grading/Artifact EDSL/Grading/CallStack/Artifact tests/fixtures/CallStack/Covered; do
    printf 'Untrusted LEAN_PATH sentinel; deliberately not a Lean object\n' > "$poison/$module.olean"
done
expect_case 4 "$unknown" isolation/poisoned-client-reference-only \
    lake env env LEAN_PATH="$poison" .lake/build/bin/edsl-grade-call-stack \
    5 "$output/compiler/gccSame/text.bin" "$reference"
if $inline_ready; then
    accept isolation/poisoned-inline-raw 5 lake env env LEAN_PATH="$poison" \
        .lake/build/bin/edsl-grade-call-stack 0 "$inline_raw" "$inline_packet"
    accept isolation/poisoned-inline-elf 5 lake env env LEAN_PATH="$poison" \
        .lake/build/bin/edsl-grade-call-stack --elf 5 0 "$inline_elf" "$inline_packet"
else
    skip_case isolation/poisoned-inline 'required inline packet unavailable'
fi
if "${packet_ready[0]}"; then
    accept isolation/poisoned-compiler-raw 14 lake env env LEAN_PATH="$poison" \
        .lake/build/bin/edsl-grade-call-stack 5 "$output/compiler/gccSame/text.bin" "$output/packets/gccSame.json"
else
    skip_case isolation/poisoned-compiler 'required gccSame packet unavailable'
fi
end_phase

begin_phase source-stability
run sha256sum -c "$output/source-SHA256SUMS" > "$output/source-stability.log" 2>&1
run sha256sum -c "$output/metadata/grader-exporter-SHA256SUMS" > "$output/installation-stability.log" 2>&1
end_phase
suite_complete=true
if [[ $failures != 0 ]]; then exit 1; fi
