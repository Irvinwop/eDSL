#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# The caller holds /tmp/edsl-lean-build.lock throughout this script. In
# particular, do not acquire it here: the native master calls us under flock.
set -euo pipefail
umask 022
export PATH="/home/irvin/.elan/bin:$PATH" LC_ALL=C TZ=UTC LEAN_NUM_THREADS=1
if [[ $# != 3 ]]; then
    echo 'usage: scripts/check-call-memory64-grading.sh OUTPUT GCC_TEXT CLANG_TEXT' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=$1
inputs=("$2" "$3")
mkdir -p -- "$output"
output=$(cd "$output" && pwd -P)
if ! existing=$(find "$output" -mindepth 1 -maxdepth 1 -print -quit); then
    echo 'Callable DATA8 grading requires a readable empty OUTPUT directory' >&2
    exit 2
fi
if [[ -n $existing ]]; then
    echo 'Callable DATA8 grading requires an empty OUTPUT directory' >&2
    exit 2
fi

profiles=(gccSeparate clangSeparate)
compiler_names=(gcc13 clang18)
phases=(sources script-checks tools build accounting installation
    compiler-artifacts inline-artifacts compiler-packets inline-packet
    compiler-grades inline-grades protocol negatives container-reuse isolation
    source-stability input-stability installation-stability)
declare -A phase_status
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
phase=setup
sequence=0
failures=0
phase_start_failures=0
suite_complete=false
command_ok=false
case_ok=false
compiler_accepts=0
inline_accepts=0
packet_ready=(false false)
inline_ready=false
source_ready=false
installation_ready=false
lean_prefix=
stability_receipts=()
exec 3>"$output/commands.log" 4>"$output/command-status.tsv" 5>"$output/case-status.tsv" 6>&2
printf 'tag\tphase\texit\n' >&4
printf 'case\tcategory\texpected\tobserved\tresult\tdiagnostic\n' >&5

run() {
    sequence=$((sequence + 1))
    local status=0 line arguments tag="$BASHPID.$sequence"
    printf -v arguments '%q ' "$@"
    printf -v line '[%s] phase=%s cwd=%q argv=%s\n' "$tag" "$phase" "$PWD" "$arguments"
    # A single write per record, including in command substitutions. BASHPID
    # distinguishes subshells whose sequence counters start from the same value.
    printf '%s' "$line" >&3
    "$@" || status=$?
    printf '%s\t%s\t%d\n' "$tag" "$phase" "$status" >&4
    return "$status"
}
failure() {
    failures=$((failures + 1))
    # Keep phase failures visible even when the command's output is redirected.
    printf 'Callable DATA8 grading: %s (see %s)\n' "$1" "$output" >&6
}
checked() {
    local status=0
    run "$@" || status=$?
    command_ok=false
    if [[ $status == 0 ]]; then command_ok=true;
    else failure "command failed: $1 (exit=$status)"; fi
    # Independent phases must still run after a missing dependency or failure.
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
    if [[ $failures == "$phase_start_failures" ]]; then phase_status[$phase]=PASS;
    else phase_status[$phase]=FAIL; fi
    write_phases
}
manifest() {
    (
        cd "$output" || exit 1
        # Materialize enumeration: process substitution would hide find/sort
        # errors. Exclude only these root manifest files, not nested receipts.
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
    printf 'grading=%s compiler_raw_elf=%d/4 inline_raw_elf=%d/4 native_inline=NOTRUN failures=%d\n' \
        "$result" "$compiler_accepts" "$inline_accepts" "$failures" > "$output/result.txt"
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
    fi
    if [[ $result != PASS && $status == 0 ]]; then status=1; fi
    if ! write_terminal "$status" "$result"; then status=1; result=FAIL; fi
    exec 3>&- 4>&- 5>&- 6>&-
    if ! manifest; then
        status=1
        result=FAIL
        failures=$((failures + 1))
        write_terminal "$status" "$result"
        printf 'Evidence manifest failed\n' > "$output/manifest-error.txt"
        manifest
    fi
    printf 'Callable DATA8 grading: %s; evidence=%s\n' "$result" "$output" >&2
    exit "$status"
}
trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

# Each invocation is a NEW CLI process with one packet. Lean's kernel heartbeat
# counter accumulates per thread; do not combine these into an in-process loop.
# Exact status AND complete diagnostic are required. Status 6, timeouts, signals
# and I/O failures cannot satisfy a semantic rejection case.
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
    expect_case 0 "^ACCEPTED: fixed callable DATA8 contract, exact artifact, selected entry and current OS resources; codeBytes=$length, auxiliaryDeclarations=[0-9]+, decoderSteps=[0-9]+, kernelChecks=[0-9]+$" \
        "$name" acceptance "$@"
}
remember_hashes() {
    local receipt=$1
    shift
    checked sha256sum -- "$@" > "$receipt" 2> "$receipt.stderr"
    if $command_ok; then stability_receipts+=("$receipt"); fi
}
public_snapshot() {
    local prefix=$1 source
    run git ls-files --cached --others --exclude-standard -z -- . > "$prefix.git-files.list0" || return
    : > "$prefix.files.list0"
    while IFS= read -r -d '' source; do
        if [[ $PWD/$source == "$output" || $PWD/$source == "$output/"* ]]; then continue; fi
        if [[ ! -f $source && ! -L $source ]]; then
            printf 'Public source missing or unsupported: %q\n' "$source" >&2
            return 1
        fi
        printf '%s\0' "$source" >> "$prefix.files.list0"
    done < "$prefix.git-files.list0"
    run sort -zu -o "$prefix.files.list0" "$prefix.files.list0" || return
    [[ -s $prefix.files.list0 ]] || return 1
    run xargs -0 -r sha256sum -- < "$prefix.files.list0" > "$prefix.file-SHA256SUMS" || return
    # Canonical metadata preserves modes and symlinks without mtime noise.
    run tar --format=gnu --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
        --null --verbatim-files-from --no-recursion -T "$prefix.files.list0" -cf "$prefix.tar" || return
    run sha256sum -- "$prefix.tar" > "$prefix.SHA256SUMS"
}
installation_snapshot() {
    local prefix=$1
    [[ -n $lean_prefix ]] || return 1
    run find .lake/build/lib/lean "$lean_prefix/lib/lean" \( -type f -o -type l \) \
        \( -name '*.olean' -o -name '*.olean.private' -o -name '*.olean.server' \
        -o -name '*.so' -o -name '*.so.*' \) -print0 > "$prefix.unsorted.list0" || return
    printf '%s\0' .lake/build/bin/edsl-grade-call-memory64 .lake/build/bin/edsl-proof-export \
        "$lean_prefix/bin/lean" "$lean_prefix/bin/lake" "$lean_prefix/bin/leanchecker" >> "$prefix.unsorted.list0"
    run sort -zu "$prefix.unsorted.list0" > "$prefix.files.list0" || return
    run xargs -0 -r sha256sum -- < "$prefix.files.list0" > "$prefix.SHA256SUMS"
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
unsupported='EDSLGrader.Runtime.FailureKind.unsupported: callable DATA8 artifact admission failed; no defect conclusion'
unknown='EDSLGrader.Runtime.FailureKind.malformed: unknown constant; no defect conclusion'
resource='EDSLGrader.Runtime.FailureKind.resource: file bytes; no defect conclusion'
internal='internal: IO or trusted installation failure; no defect conclusion'
usage='usage: edsl-grade-call-memory64 [--elf SPAN_BYTES] ENTRY_OFFSET INPUT PROOF.json; no defect conclusion'
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade-call-memory64)

begin_phase sources
mkdir -p "$output/metadata" "$output/compiler" "$output/inline" "$output/packets" "$output/negative"
if public_snapshot "$output/public-source" > "$output/source-snapshot.log" 2>&1; then source_ready=true;
else failure 'initial public source snapshot failed'; fi
checked git rev-parse HEAD > "$output/metadata/HEAD.txt" 2>&1
checked git status --short --branch --untracked-files=all > "$output/metadata/worktree.txt" 2>&1
cat > "$output/scope.txt" <<'SCOPE'
Owned synthetic callable DATA8 artifacts only. The two previously authenticated
18-byte nested-call inputs and their complete sibling ELFs are copied as DATA.
Each whole raw text and full ELF is graded against the independent universal
CallMemory64 contract with entry0 and ELF span18, including the helper after
the caller RET. There is no first-RET scan, compiler-profile admission whitelist,
instruction-count condition or read-order condition in acceptance.

Fresh GCC13 and Clang18 compile the inline fixture using the unchanged native
runner's compile/link flags. Both actual eight-byte raw texts and full ELFs must
accept the same independently exported Inline.claim. These are proof-only
artifact grades; no native inline observations are made or claimed. The parent
runner owns nested native observations and formal validation. Separate inline
accounting is built with warnings as errors, never used as an admission filter.
No raw inputs, input ELFs or compiler-generated fixture objects are executed.

Only the client exporter imports a named built client module. The grader takes
proof JSON data and fixes its installed imports, contract and default budgets.
Every case uses one fresh CLI process; the cumulative kernel heartbeat counter
is never reused for a second candidate. Reference-only packets must fail even
with the client module built. Poisoned LEAN_PATH contains corrupt object-file
sentinels, including all fixed foundation modules and the client modules.

Program proofs may legitimately be reused for the same program in a different
ELF container: the grader checks a new exact-file artifact wrapper. Nonloaded
container notes test that acceptance boundary. Mutated selected code, entry or
invalid backing metadata are separate negative cases. Exact status and complete
diagnostic distinguish semantic rejection from resource exhaustion, timeout,
signal and I/O failure. Explicit resource and I/O protocol checks are separately
categorized and never credited as semantic rejections. Proof failure and all
other unsuccessful outcomes establish no security defect.

The full public source snapshot includes dirty and untracked nonignored files;
ignored private storage, build output and this evidence directory are excluded.
Sources, original/copy inputs, proof packets, compiler flags/tool versions,
installed Lean objects/tools, command statuses and case output are retained or
hashed, with final source/input/installation stability checks and a manifest.
Environmental assumptions remain those of the fixed Lean theorem contracts and
trusted pinned Lean/CLI installation. This is not compiler preservation, native
CPU correspondence or a Linux process-startup proof.
SCOPE
end_phase

begin_phase script-checks
checked bash -n scripts/check-call-memory64-grading.sh > "$output/bash-n.log" 2>&1
checked shellcheck -s bash scripts/check-call-memory64-grading.sh > "$output/shellcheck.log" 2>&1
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
    for tool in ld as objcopy readelf objdump nm shellcheck; do checked "/usr/bin/$tool" --version; done
} > "$output/metadata/tools.txt" 2>&1
checked /usr/bin/gcc-13 -dumpfullversion > "$output/metadata/gcc-version.txt" 2>&1
checked /usr/bin/clang-18 --version > "$output/metadata/clang-version.txt" 2>&1
checked grep -Eq '^13\.' "$output/metadata/gcc-version.txt"
checked grep -Eq 'clang version 18\.' "$output/metadata/clang-version.txt"
checked lake env lean --version > "$output/metadata/lean-version.txt" 2>&1
pinned=$(< lean-toolchain)
if [[ $pinned =~ ^leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)$ ]]; then
    checked grep -Fq "version ${BASH_REMATCH[1]}," "$output/metadata/lean-version.txt"
else failure 'unsupported Lean toolchain pin'; fi
checked lake env lean --print-prefix > "$output/metadata/lean-prefix.txt" 2> "$output/metadata/lean-prefix.stderr"
if $command_ok; then
    lean_prefix=$(< "$output/metadata/lean-prefix.txt")
    checked readlink -f -- "$lean_prefix" > "$output/metadata/lean-prefix-real.txt" 2>&1
    if $command_ok; then lean_prefix=$(< "$output/metadata/lean-prefix-real.txt"); else lean_prefix=; fi
fi
checked sha256sum /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as \
    /usr/bin/objcopy /usr/bin/readelf /usr/bin/objdump /usr/bin/nm /usr/bin/shellcheck \
    > "$output/metadata/tool-SHA256SUMS" 2> "$output/metadata/tool-hash.stderr"
end_phase

begin_phase build
checked lake build edsl-grade-call-memory64 edsl-proof-export tests.fixtures.CallMemory64.Covered \
    > "$output/build.log" 2>&1
end_phase

begin_phase accounting
accounting_target=tests.fixtures.CallMemory64.Inline
if [[ -f tests/fixtures/CallMemory64/Inline/Accounting.lean ]]; then
    accounting_target=tests.fixtures.CallMemory64.Inline.Accounting
fi
printf '%s\n' "$accounting_target" > "$output/metadata/accounting-target.txt"
checked lake build "$accounting_target" > "$output/accounting-build.log" 2>&1
end_phase

begin_phase installation
if installation_snapshot "$output/metadata/installation" > "$output/installation-snapshot.log" 2>&1; then
    installation_ready=true
else failure 'installed CLI/exporter/Lean snapshot failed'; fi
end_phase

begin_phase compiler-artifacts
printf 'profile\toriginal_raw\toriginal_elf\tentry\tspan\n' > "$output/compiler-inputs.tsv"
for index in 0 1; do
    profile=${profiles[index]}
    directory="$output/compiler/$profile"
    mkdir -p "$directory"
    original=${inputs[index]}
    original_elf="$(run dirname -- "$original")/function.elf"
    checked realpath -e -- "$original" > "$directory/original-raw-path.txt" 2> "$directory/original-raw-path.stderr"
    if $command_ok; then original=$(< "$directory/original-raw-path.txt"); fi
    checked realpath -e -- "$original_elf" > "$directory/original-elf-path.txt" 2> "$directory/original-elf-path.stderr"
    if $command_ok; then original_elf=$(< "$directory/original-elf-path.txt"); fi
    printf '%s\t%s\t%s\t0\t18\n' "$profile" "$original" "$original_elf" >> "$output/compiler-inputs.tsv"
    remember_hashes "$directory/original-SHA256SUMS" "$original" "$original_elf"
    checked cp -- "$original" "$directory/text.bin" > "$directory/copy-raw.log" 2>&1
    checked cp -- "$original_elf" "$directory/function.elf" > "$directory/copy-elf.log" 2>&1
    checked cmp "$original" "$directory/text.bin" > "$directory/original-raw-binding.log" 2>&1
    checked cmp "$original_elf" "$directory/function.elf" > "$directory/original-elf-binding.log" 2>&1
    inspect_artifact "$directory" 18
    remember_hashes "$directory/artifact-SHA256SUMS" "$directory/text.bin" "$directory/function.elf"
done
end_phase

begin_phase inline-artifacts
# These are exactly verify-call-memory64.sh's flags. No tuning for inline code.
flags=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-stack-protector -fno-unwind-tables
    -fno-asynchronous-unwind-tables -fno-optimize-sibling-calls)
link_flags=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e caller -Ttext=0x401000)
{
    printf 'compiler_flags='; printf '%q ' "${flags[@]}"; printf '\n'
    printf 'linker_flags='; printf '%q ' "${link_flags[@]}"; printf '\n'
} > "$output/metadata/flags.txt"
printf '\110\211\067\110\215\106\001\303' > "$output/inline/expected-text.bin"
for compiler_name in "${compiler_names[@]}"; do
    if [[ $compiler_name == gcc13 ]]; then compiler=/usr/bin/gcc-13; else compiler=/usr/bin/clang-18; fi
    directory="$output/inline/$compiler_name"
    mkdir -p "$directory"
    checked "$compiler" "${flags[@]}" -c fixtures/call-memory64-inline.c -o "$directory/function.o" \
        > "$directory/compile.log" 2>&1
    checked /usr/bin/ld "${link_flags[@]}" "$directory/function.o" -o "$directory/function.elf" \
        > "$directory/link.log" 2>&1
    checked /usr/bin/objcopy -O binary --only-section=.text "$directory/function.elf" "$directory/text.bin" \
        > "$directory/objcopy.log" 2>&1
    inspect_artifact "$directory" 8
    checked cmp "$output/inline/expected-text.bin" "$directory/text.bin" > "$directory/compiler-profile.log" 2>&1
    checked /usr/bin/objdump -drwC -Mintel --show-raw-insn "$directory/function.o" > "$directory/object-disassembly.txt" 2>&1
    remember_hashes "$directory/artifact-SHA256SUMS" "$directory/function.o" "$directory/function.elf" "$directory/text.bin"
done
end_phase

export_pattern='^EXPORTED: client packet; auxiliaryDeclarations=[1-9][0-9]*, declaredNames=[1-9][0-9]*, bytes=[1-9][0-9]*\. Submit to the matching fixed-contract grader for artifact checking\.$'
begin_phase compiler-packets
for index in 0 1; do
    profile=${profiles[index]}
    packet="$output/packets/$profile.json"
    expect_case 0 "$export_pattern" "export-$profile" export \
        "${exporter[@]}" tests.fixtures.CallMemory64.Covered "EDSL.CallMemory64.Client.$profile" "$packet"
    if $case_ok; then
        if [[ -s $packet ]]; then
            packet_ready[index]=true
            remember_hashes "$packet.SHA256SUMS" "$packet"
        else failure "$profile exporter produced no packet"; fi
    fi
done
end_phase

begin_phase inline-packet
inline_packet="$output/packets/inline.json"
expect_case 0 "$export_pattern" export-inline export \
    "${exporter[@]}" tests.fixtures.CallMemory64.Inline EDSL.CallMemory64.Inline.claim "$inline_packet"
if $case_ok; then
    if [[ -s $inline_packet ]]; then
        inline_ready=true
        remember_hashes "$inline_packet.SHA256SUMS" "$inline_packet"
    else failure 'inline exporter produced no packet'; fi
fi
end_phase

begin_phase compiler-grades
for index in 0 1; do
    profile=${profiles[index]}
    directory="$output/compiler/$profile"
    packet="$output/packets/$profile.json"
    if ! "${packet_ready[index]}"; then
        unavailable "$profile/raw" 'required compiler packet unavailable'
        unavailable "$profile/elf" 'required compiler packet unavailable'
        continue
    fi
    accept "$profile/raw" 18 "${grader[@]}" 0 "$directory/text.bin" "$packet"
    if $case_ok; then compiler_accepts=$((compiler_accepts + 1)); fi
    accept "$profile/elf" 18 "${grader[@]}" --elf 18 0 "$directory/function.elf" "$packet"
    if $case_ok; then compiler_accepts=$((compiler_accepts + 1)); fi
done
if [[ $compiler_accepts != 4 ]]; then failure 'all two compiler raw+ELF grades are required at default limits'; fi
end_phase

begin_phase inline-grades
for compiler_name in "${compiler_names[@]}"; do
    directory="$output/inline/$compiler_name"
    if ! $inline_ready; then
        unavailable "inline-$compiler_name/raw" 'required inline packet unavailable'
        unavailable "inline-$compiler_name/elf" 'required inline packet unavailable'
        continue
    fi
    accept "inline-$compiler_name/raw" 8 "${grader[@]}" 0 "$directory/text.bin" "$inline_packet"
    if $case_ok; then inline_accepts=$((inline_accepts + 1)); fi
    accept "inline-$compiler_name/elf" 8 "${grader[@]}" --elf 8 0 "$directory/function.elf" "$inline_packet"
    if $case_ok; then inline_accepts=$((inline_accepts + 1)); fi
done
if [[ $inline_accepts != 4 ]]; then failure 'both fresh inline compiler raw+ELF grades are required at default limits'; fi
end_phase

begin_phase protocol
foreign="$output/packets/foreign-write-v1.json"
# A real trusted theorem for an existing fixed task tests engine separation.
printf '%s\n' '["edsl-proof-v1",[],["const",["EDSL","Grading","Known","write"],[]]]' > "$foreign"
printf '\377' > "$output/negative/unsupported.bin"
printf '\377' > "$output/packets/invalid-utf8.json"
printf '%s\n' '["edsl-proof-v1",,[],[]]' > "$output/packets/invalid-json.json"
: > "$output/negative/empty.bin"
expect_case 2 "$usage" protocol/usage protocol-usage "${grader[@]}"
expect_case 2 "$usage" protocol/negative-entry protocol-usage "${grader[@]}" -1 "$output/negative/unsupported.bin" "$foreign"
expect_case 2 "$usage" protocol/nondecimal-span protocol-usage "${grader[@]}" --elf bad 0 "$output/negative/unsupported.bin" "$foreign"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: proof UTF-8; no defect conclusion' \
    protocol/proof-utf8 malformed "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/invalid-utf8.json"
expect_case 4 'EDSLGrader.Runtime.FailureKind.malformed: JSON syntax; no defect conclusion' \
    protocol/proof-json malformed "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/invalid-json.json"
checked dd if=/dev/zero of="$output/negative/oversized-raw.bin" bs=4097 count=1 status=none
checked dd if=/dev/zero of="$output/negative/oversized-elf.bin" bs=65537 count=1 status=none
checked dd if=/dev/zero of="$output/packets/oversized.json" bs=4194305 count=1 status=none
expect_case 6 "$resource" protocol/raw-byte-limit protocol-resource "${grader[@]}" 0 "$output/negative/oversized-raw.bin" "$foreign"
expect_case 6 "$resource" protocol/elf-byte-limit protocol-resource "${grader[@]}" --elf 18 0 "$output/negative/oversized-elf.bin" "$foreign"
expect_case 6 "$resource" protocol/proof-byte-limit protocol-resource "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/oversized.json"
expect_case 1 "$internal" protocol/input-io protocol-io "${grader[@]}" 0 "$output/negative/nonexistent.bin" "$foreign"
expect_case 1 "$internal" protocol/proof-io protocol-io "${grader[@]}" 0 "$output/negative/unsupported.bin" "$output/packets/nonexistent.json"
end_phase

begin_phase negatives
expect_case 5 "$rejected" negative/foreign-legacy-task semantic "${grader[@]}" 0 "$output/negative/unsupported.bin" "$foreign"
expect_case 3 "$unsupported" negative/empty-raw unsupported "${grader[@]}" 0 "$output/negative/empty.bin" "$foreign"
expect_case 3 "$unsupported" negative/raw-entry-out-of-bounds unsupported "${grader[@]}" 1 "$output/negative/unsupported.bin" "$foreign"
printf '\213' > "$output/negative/store-patch.bin"
printf '\100' > "$output/negative/prefix-patch.bin"
for index in 0 1; do
    profile=${profiles[index]}
    original="$output/compiler/$profile/text.bin"
    packet="$output/packets/$profile.json"
    if ! "${packet_ready[index]}"; then
        unavailable "negative/$profile-proof-binding" 'required compiler packet unavailable'
        continue
    fi
    expect_case 5 "$rejected" "negative/$profile-wrong-entry" semantic "${grader[@]}" 1 "$original" "$packet"
    next=$((1 - index))
    if "${packet_ready[next]}"; then
        expect_case 5 "$rejected" "negative/$profile-cross-profile" semantic "${grader[@]}" \
            0 "$original" "$output/packets/${profiles[next]}.json"
    else unavailable "negative/$profile-cross-profile" 'required other-profile packet unavailable'; fi
    for mutation in store helper-prefix omitted-helper truncated-call truncated-helper-ret extended; do
        mutant="$output/negative/$profile-$mutation.bin"
        case $mutation in
            store|helper-prefix)
                checked cp -- "$original" "$mutant"
                if [[ $mutation == store ]]; then patch=store; position=12; else patch=prefix; position=11; fi
                checked dd if="$output/negative/$patch-patch.bin" of="$mutant" bs=1 seek="$position" count=1 conv=notrunc status=none
                ;;
            # Caller RET at offset10 must not hide the helper at offset11.
            omitted-helper) checked head -c 11 "$original" > "$mutant" ;;
            # CALL at offset1 needs five bytes, but this file ends at offset4.
            truncated-call) checked head -c 5 "$original" > "$mutant" ;;
            truncated-helper-ret) checked head -c 17 "$original" > "$mutant" ;;
            extended) checked cp -- "$original" "$mutant"; printf '\220' >> "$mutant" ;;
        esac
        expect_case 5 "$rejected" "negative/$profile-$mutation" semantic "${grader[@]}" 0 "$mutant" "$packet"
    done
    changed_elf="$output/negative/$profile-store.elf"
    checked /usr/bin/objcopy --update-section ".text=$output/negative/$profile-store.bin" \
        "$output/compiler/$profile/function.elf" "$changed_elf" > "$changed_elf.objcopy.log" 2>&1
    expect_case 5 "$rejected" "negative/$profile-elf-selected-code" semantic "${grader[@]}" --elf 18 0 "$changed_elf" "$packet"
    expect_case 5 "$rejected" "negative/$profile-short-elf-span" semantic "${grader[@]}" --elf 17 0 "$output/compiler/$profile/function.elf" "$packet"
done
if $inline_ready; then
    expect_case 5 "$rejected" negative/inline-wrong-entry semantic "${grader[@]}" 1 "$output/inline/gcc13/text.bin" "$inline_packet"
    checked cp -- "$output/inline/gcc13/text.bin" "$output/negative/inline-extended.bin"
    printf '\220' >> "$output/negative/inline-extended.bin"
    expect_case 5 "$rejected" negative/inline-extended semantic "${grader[@]}" 0 "$output/negative/inline-extended.bin" "$inline_packet"
else unavailable negative/inline-proof-binding 'required inline packet unavailable'; fi

elf="$output/compiler/gccSeparate/function.elf"
expect_case 3 "$unsupported" negative/empty-elf unsupported "${grader[@]}" --elf 18 0 "$output/negative/empty.bin" "$foreign"
expect_case 3 "$unsupported" negative/empty-elf-span unsupported "${grader[@]}" --elf 0 0 "$elf" "$foreign"
expect_case 3 "$unsupported" negative/elf-entry-out-of-bounds unsupported "${grader[@]}" --elf 18 18 "$elf" "$foreign"
expect_case 3 "$unsupported" negative/elf-wrong-selected-entry unsupported "${grader[@]}" --elf 18 1 "$elf" "$foreign"
expect_case 3 "$unsupported" negative/elf-overrun-span unsupported "${grader[@]}" --elf 19 0 "$elf" "$foreign"
checked cp -- "$elf" "$output/negative/changed-entry.elf"
# ELF64LE e_entry at byte24: 0x401000 -> 0x401001.
printf '\001\020\100\000\000\000\000\000' > "$output/negative/entry-patch.bin"
checked dd if="$output/negative/entry-patch.bin" of="$output/negative/changed-entry.elf" \
    bs=1 seek=24 count=8 conv=notrunc status=none
checked /usr/bin/readelf -hW "$output/negative/changed-entry.elf" > "$output/negative/changed-entry.readelf.txt" 2>&1
expect_case 3 "$unsupported" negative/changed-elf-entry unsupported "${grader[@]}" --elf 18 0 "$output/negative/changed-entry.elf" "$foreign"

# Locate the actual executable PT_LOAD header rather than assuming its index.
# All arithmetic here is bounded to the owned <=64KiB fixture. GNU od decodes
# little endian explicitly, independently of the host's byte order.
program_offset=$(run od --endian=little -An -v -tu8 -j 32 -N 8 "$elf") || program_offset=
program_count=$(run od --endian=little -An -v -tu2 -j 56 -N 2 "$elf") || program_count=
executable_header=
if [[ $program_offset =~ ^[[:space:]]*[0-9]+[[:space:]]*$ && $program_count =~ ^[[:space:]]*[0-9]+[[:space:]]*$ ]] &&
    (( program_offset >= 64 && program_count > 0 && program_count <= 16 && program_offset + program_count * 56 <= 65536 )); then
    for ((index=0; index<program_count; index++)); do
        base=$((program_offset + index * 56))
        kind=$(run od --endian=little -An -v -tu4 -j "$base" -N 4 "$elf") || kind=
        permissions=$(run od --endian=little -An -v -tu4 -j "$((base + 4))" -N 4 "$elf") || permissions=
        if [[ $kind =~ ^[[:space:]]*[0-9]+[[:space:]]*$ && $permissions =~ ^[[:space:]]*[0-9]+[[:space:]]*$ ]] &&
            (( kind == 1 && (permissions & 1) == 1 )); then executable_header=$base; break; fi
    done
fi
if [[ -n $executable_header ]]; then
    printf 'executable_program_header_file_offset=%d\n' "$executable_header" > "$output/negative/backing-binding.txt"
    checked cp -- "$elf" "$output/negative/unbacked-window.elf"
    # Keep the entry file-backed and the rest BSS: parse can succeed, but the
    # full selected window is not backed by file bytes. p_filesz is at +32.
    printf '\001\000\000\000\000\000\000\000' > "$output/negative/backing-patch.bin"
    checked dd if="$output/negative/backing-patch.bin" of="$output/negative/unbacked-window.elf" \
        bs=1 seek="$((executable_header + 32))" count=8 conv=notrunc status=none
    checked /usr/bin/readelf -lW "$output/negative/unbacked-window.elf" > "$output/negative/unbacked-window.readelf.txt" 2>&1
    expect_case 3 "$unsupported" negative/elf-unbacked-window unsupported "${grader[@]}" --elf 18 0 "$output/negative/unbacked-window.elf" "$foreign"
else unavailable negative/elf-unbacked-window 'could not locate owned executable PT_LOAD'; fi
end_phase

begin_phase container-reuse
printf 'Owned nonloaded grading note: a different ELF literal, the same selected program.\n' > "$output/metadata/container-note.txt"
for index in 0 1; do
    profile=${profiles[index]}
    directory="$output/compiler/$profile/container-note"
    mkdir -p "$directory"
    checked /usr/bin/objcopy --add-section ".edsl_grading=$output/metadata/container-note.txt" \
        "$output/compiler/$profile/function.elf" "$directory/function.elf" > "$directory/objcopy.log" 2>&1
    difference=0
    run cmp -s "$output/compiler/$profile/function.elf" "$directory/function.elf" || difference=$?
    if [[ $difference != 1 ]]; then failure "$profile: container must differ with cmp status1, observed=$difference"; fi
    checked cp -- "$output/compiler/$profile/text.bin" "$directory/text.bin"
    inspect_artifact "$directory" 18
    remember_hashes "$directory/artifact-SHA256SUMS" "$directory/text.bin" "$directory/function.elf"
    if "${packet_ready[index]}"; then
        accept "container-reuse/$profile" 18 "${grader[@]}" --elf 18 0 "$directory/function.elf" "$output/packets/$profile.json"
    else unavailable "container-reuse/$profile" 'required compiler packet unavailable'; fi
done
end_phase

begin_phase isolation
poison="$output/poison"
mkdir -p "$poison/EDSL/Grading/CallStack" "$poison/EDSL/Grading/CallMemory64" "$poison/tests/fixtures/CallMemory64"
for module in EDSL/Grading/Known EDSL/Grading/Artifact EDSL/Grading/CallStack/Artifact \
    EDSL/Grading/CallMemory64/Artifact EDSL/Grading/CallMemoryLoop64/Artifact \
    EDSL/Grading/AtomicLogical64/Artifact EDSL/Grading/AtomicSet64/Artifact \
    tests/fixtures/CallMemory64/Covered tests/fixtures/CallMemory64/Inline; do
    mkdir -p "$poison/${module%/*}"
    printf 'Untrusted LEAN_PATH sentinel; deliberately not a Lean object\n' > "$poison/$module.olean"
done
for index in 0 1; do
    profile=${profiles[index]}
    reference="$output/packets/$profile-reference-only-v1.json"
    printf '["edsl-proof-v1",[],["const",["EDSL","CallMemory64","Client","%s"],[]]]\n' "$profile" > "$reference"
    expect_case 4 "$unknown" "isolation/$profile-reference-only" isolation "${grader[@]}" 0 "$output/compiler/$profile/text.bin" "$reference"
    expect_case 4 "$unknown" "isolation/$profile-poisoned-reference-only" isolation \
        lake env env LEAN_PATH="$poison" .lake/build/bin/edsl-grade-call-memory64 0 "$output/compiler/$profile/text.bin" "$reference"
    if "${packet_ready[index]}"; then
        accept "isolation/$profile-poisoned-raw" 18 lake env env LEAN_PATH="$poison" \
            .lake/build/bin/edsl-grade-call-memory64 0 "$output/compiler/$profile/text.bin" "$output/packets/$profile.json"
        accept "isolation/$profile-poisoned-elf" 18 lake env env LEAN_PATH="$poison" \
            .lake/build/bin/edsl-grade-call-memory64 --elf 18 0 "$output/compiler/$profile/function.elf" "$output/packets/$profile.json"
    else unavailable "isolation/$profile-poisoned-packet" 'required compiler packet unavailable'; fi
done
reference="$output/packets/inline-reference-only-v1.json"
printf '%s\n' '["edsl-proof-v1",[],["const",["EDSL","CallMemory64","Inline","claim"],[]]]' > "$reference"
expect_case 4 "$unknown" isolation/inline-reference-only isolation "${grader[@]}" 0 "$output/inline/gcc13/text.bin" "$reference"
expect_case 4 "$unknown" isolation/inline-poisoned-reference-only isolation \
    lake env env LEAN_PATH="$poison" .lake/build/bin/edsl-grade-call-memory64 0 "$output/inline/gcc13/text.bin" "$reference"
if $inline_ready; then
    accept isolation/inline-poisoned-raw 8 lake env env LEAN_PATH="$poison" \
        .lake/build/bin/edsl-grade-call-memory64 0 "$output/inline/gcc13/text.bin" "$inline_packet"
    accept isolation/inline-poisoned-elf 8 lake env env LEAN_PATH="$poison" \
        .lake/build/bin/edsl-grade-call-memory64 --elf 8 0 "$output/inline/gcc13/function.elf" "$inline_packet"
else unavailable isolation/inline-poisoned-packet 'required inline packet unavailable'; fi
end_phase

begin_phase source-stability
if public_snapshot "$output/public-source-final" > "$output/source-final-snapshot.log" 2>&1; then
    if $source_ready; then
        checked cmp "$output/public-source.files.list0" "$output/public-source-final.files.list0" > "$output/source-list-stability.log" 2>&1
        checked cmp "$output/public-source.tar" "$output/public-source-final.tar" > "$output/source-stability.log" 2>&1
        checked sha256sum -c "$output/public-source.file-SHA256SUMS" > "$output/source-hash-stability.log" 2>&1
    else failure 'initial source snapshot unavailable'; fi
else failure 'final public source snapshot failed'; fi
checked git rev-parse HEAD > "$output/metadata/final-HEAD.txt" 2>&1
checked cmp "$output/metadata/HEAD.txt" "$output/metadata/final-HEAD.txt" > "$output/head-stability.log" 2>&1
end_phase

begin_phase input-stability
# 2 original pairs + 2 copied pairs + 2 inline triples + 3 exported packets
# + 2 alternate containers. Missing hash receipts cannot be a successful phase.
if [[ ${#stability_receipts[@]} != 11 ]]; then failure 'not all eleven required input/packet hash receipts were captured'; fi
for receipt in "${stability_receipts[@]}"; do
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
    else failure 'initial installation snapshot unavailable'; fi
else failure 'final installation snapshot failed'; fi
checked sha256sum -c "$output/metadata/tool-SHA256SUMS" > "$output/tool-stability.log" 2>&1
end_phase
suite_complete=true
if [[ $failures != 0 ]]; then exit 1; fi
