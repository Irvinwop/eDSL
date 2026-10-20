#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Explicit native-only gate. Root owns the separate future formal integration.
set -euo pipefail
umask 022
export LC_ALL=C TZ=UTC
if (( $# > 1 )); then
    echo 'usage: scripts/verify-call-memory-loop64-native.sh [EMPTY_OUTPUT_DIRECTORY]' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Counted DATA8 native evidence requires Linux x86_64' >&2
    exit 2
fi
exec 9>/tmp/edsl-call-memory-loop64-native-home.lock
if ! flock -n 9; then
    echo 'A counted DATA8 native gate is already active' >&2
    exit 2
fi
evidence_root=${CALL_MEMORY_LOOP64_EVIDENCE_ROOT:-$PWD/.cache/call-memory-loop64-native}
if (( $# )); then
    candidate=$1
else
    candidate=$evidence_root/run-$(date -u +%Y%m%dT%H%M%S)-$$
fi
if [[ -L $candidate ]]; then
    echo 'Output must be an empty real directory; refusing overwrite' >&2
    exit 2
fi
output=$(realpath -m -- "$candidate")
if [[ $PWD == "$output" || $PWD == "$output/"* ]]; then
    echo 'The evidence output must not contain the source checkout' >&2
    exit 2
fi
if [[ $output == "$PWD/"* ]] && ! git check-ignore -q -- "$output"; then
    echo 'In-repository evidence output must be ignored by git' >&2
    exit 2
fi
if [[ -e $output ]]; then
    if [[ ! -d $output ]]; then
        echo 'Output must be an empty real directory; refusing overwrite' >&2
        exit 2
    fi
    if ! existing=$(find "$output" -mindepth 1 -maxdepth 1 -print -quit 2>/dev/null); then
        echo 'Output must be a readable empty directory; refusing overwrite' >&2
        exit 2
    fi
    if [[ -n $existing ]]; then
        echo 'Output must be an empty real directory; refusing overwrite' >&2
        exit 2
    fi
else
    mkdir -p -- "${output%/*}"
    mkdir -- "$output"
fi
printf 'Counted DATA8 native evidence: %s\n' "$output" >&2
exec 3>"$output/commands.log" 4>"$output/command-status.tsv"
sequence=0
phases=(syntax snapshot toolchain compilation authentication rejections native replay coverage source_stability)
declare -A phase_status
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
rejection_count=0 guard_count=0 observer_count=0 positive_count=0 negative_count=0
overall=FAIL
texts=()
sources=(fixtures/call-memory-loop64-check.c fixtures/call-memory-loop64-check.S
    scripts/verify-call-memory-loop64-native.sh fixtures/call-memory-loop64-caller.c
    fixtures/call-memory-loop64-helper.c tests/fixtures/CallMemoryLoop64Programs.lean)
run() {
    sequence=$((sequence + 1))
    local status=0 arguments tag="$BASHPID.$sequence"
    printf -v arguments '%q ' "$@"
    printf '[%s] cwd=%q argv=%s\n' "$tag" "$PWD" "$arguments" >&3
    "$@" || status=$?
    printf '%s\t%d\n' "$tag" "$status" >&4
    return "$status"
}
phase_begin() {
    phase_status[$1]=RUNNING
    printf 'phase=%s status=RUNNING UTC=%s\n' "$1" "$(date -u +%FT%TZ)" >&2
}
phase_pass() { phase_status[$1]=PASS; }
write_terminal() {
    local status=$1 native=NOTRUN
    if [[ $overall == PASS ]]; then native=PASS
    elif [[ ${phase_status[native]} != NOTRUN ]]; then native=FAIL; fi
    printf 'overall=%s native=%s formal=NOTRUN native_only=true observers=%d compiler_profiles=%d extraction_rejections=%d guard_rejections=%d positive=%d negative=%d flag_profiles_per_observer=128 counts_per_profile=8 inputs_per_count=8 source_stability=%s\n' \
        "$overall" "$native" "$observer_count" "${#texts[@]}" "$rejection_count" "$guard_count" \
        "$positive_count" "$negative_count" "${phase_status[source_stability]}" > "$output/result.txt"
    printf 'phase\tstatus\n' > "$output/phase-status.tsv"
    local phase
    for phase in "${phases[@]}"; do
        printf '%s\t%s\n' "$phase" "${phase_status[$phase]}" >> "$output/phase-status.tsv"
    done
    printf 'formal\tNOTRUN\n' >> "$output/phase-status.tsv"
    printf 'exit=%d UTC=%s native_only=true\n' "$status" "$(date -u +%FT%TZ)" > "$output/terminal-status.txt"
}
manifest() {
    (
        cd "$output" || exit 1
        # Root checksum files exclude themselves; everything else is retained.
        # shellcheck disable=SC2094
        find . -type f ! -path ./SHA256SUMS ! -path ./MANIFEST-SHA256.txt -print0 |
            sort -z | xargs -0 -r sha256sum -- > SHA256SUMS || exit 1
        sha256sum SHA256SUMS > MANIFEST-SHA256.txt
    )
}
finish() {
    local status=$? phase
    trap - EXIT HUP INT TERM
    set +e
    for phase in "${phases[@]}"; do
        if [[ ${phase_status[$phase]} == RUNNING ]]; then phase_status[$phase]=FAIL; fi
        if [[ ${phase_status[$phase]} != PASS && $status == 0 ]]; then status=1; fi
    done
    # No early success, including an authentication-only run, can close PASS.
    if (( observer_count != 2 || positive_count != 32768 || negative_count != 1280 ||
          rejection_count != 206 || guard_count != 38 )); then
        if (( status == 0 )); then status=1; fi
    fi
    if (( status == 0 )); then overall=PASS; fi
    write_terminal "$status" || { status=1; overall=FAIL; }
    exec 3>&- 4>&-
    if ! manifest; then
        status=1; overall=FAIL
        write_terminal "$status"
        manifest
    fi
    if (( status == 0 )); then cat "$output/result.txt" >&2
    else printf 'Counted DATA8 native gate FAIL; see %s\n' "$output" >&2; fi
    exit "$status"
}
trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

phase_begin syntax
run bash -n scripts/verify-call-memory-loop64-native.sh
run /usr/bin/shellcheck -s bash scripts/verify-call-memory-loop64-native.sh > "$output/shellcheck.txt" 2>&1
phase_pass syntax

# Deliberately only these six inputs: other proof workers may change Lean files.
# Canonical tar detects byte/name/mode changes without freezing the whole repo.
snapshot() {
    local prefix=$1
    run sha256sum -- "${sources[@]}" > "$prefix.SHA256SUMS"
    printf '%s\0' "${sources[@]}" > "$prefix.files.list0"
    run tar --format=gnu --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
        --null --verbatim-files-from --no-recursion -T "$prefix.files.list0" -cf "$prefix.tar"
}
phase_begin snapshot
mkdir "$output/metadata" "$output/source"
snapshot "$output/native-source"
run tar -xf "$output/native-source.tar" -C "$output/source"
run git rev-parse HEAD > "$output/metadata/git-head.txt"
run git branch --show-current > "$output/metadata/git-branch.txt"
printf '%s\n' "${sources[@]}" > "$output/metadata/stability-scope.txt"
phase_pass snapshot

phase_begin toolchain
{
    run date -u +%FT%TZ
    run uname -a
    run cat /etc/os-release
    run /usr/bin/gcc-13 --version
    run /usr/bin/gcc-13 -dumpfullversion
    run /usr/bin/gcc-13 -dumpmachine
    run /usr/bin/gcc-13 -print-prog-name=cc1
    run /usr/bin/gcc-13 -print-prog-name=as
    run /usr/bin/clang-18 --version
    run /usr/bin/clang-18 -print-target-triple
    run /usr/bin/clang-18 -print-resource-dir
    for tool in ld as readelf objcopy objdump nm file shellcheck timeout jq; do run "/usr/bin/$tool" --version; done
    run /usr/bin/openssl version -a
    run /usr/bin/readlink -f /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as
} > "$output/metadata/platform-tools.txt" 2>&1
gcc_version=$(run /usr/bin/gcc-13 -dumpfullversion)
clang_version=$(run /usr/bin/clang-18 --version)
[[ $gcc_version == 13.* && $clang_version == *'clang version 18.'* ]]
run sha256sum /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as \
    /usr/bin/readelf /usr/bin/objcopy /usr/bin/objdump /usr/bin/nm /usr/bin/file \
    /usr/bin/shellcheck /usr/bin/openssl /usr/bin/timeout /usr/bin/jq \
    "$(run /usr/bin/gcc-13 -print-prog-name=cc1)" > "$output/metadata/tool-SHA256SUMS"
phase_pass toolchain

cat > "$output/scope.txt" <<'SCOPE'
EXPLICIT NATIVE ONLY: native=PASS requires all native phases and complete records.
formal=NOTRUN. This gate establishes no universal compiler proof,
source-preservation, hardware conformance or kernel correctness. No Lean build is run.
Stability covers exactly the owned C/assembly/runner plus caller/helper sources
and tests/fixtures/CallMemoryLoop64Programs.lean; other proof work is concurrent.
Root owns whole-project freeze and publication/integration.

Fresh separately compiled GNU23 objects and linked complete text: GCC13 45 bytes
entry0/helper38; Clang18 52 bytes entry0/helper45. Compiler/linker flags match
verify-call-memory64.sh without tuning or warm build-cache reuse. The old runner
is read-only reference, not part of this gate's stability snapshot. Full ELF,
objects, relocations, readelf and disassembly are provenance. ELF inputs are
never executed. Both data text files and both exact end-label-bounded embedded
slots authenticate before any evidence is opened or candidate code entered.
Every input byte is flipped, plus truncate/append/cross-profile substitutions,
independently per observer: exit2, exact diagnostic, empty stdout, no evidence.
Missing/empty/directory/symlink/FIFO inputs, corrupted embedded slot boundaries
(first/last bytes), output admission and auth-before-output guards also reject.
Both observers are fresh independently compiled GCC13/Clang18 PIE executables.

Ordinary Linux x86-64 SysV user RAM, canonical mapped addresses, AC/DF/TF/NT/VM
clear. Disabled CET and absence of asynchronous interference are environmental
assumptions. ARCH_SHSTK_STATUS result/status/errno and effective blocked signal
mask are recorded; unsupported query does not prove CET absent, and IBT is not
queried. SIGKILL/SIGSTOP cannot be blocked. Native endpoint evidence is bounded
to counts 0,1,2,3,7,31,257,1024; no all-full64-count theorem is claimed here.
Unaligned machine inputs make no C source semantics claim.

Entry is a JMP at S=stack page+40 (8mod16) with the original root return word
at[40,48). Actual internal CALL/RET use RAM. Private32=[page+8,page+40):
GCC RBP/RBX/padRCX/internal return at S-8/-16/-24/-32; Clang R14/RBX/padRAX
has the same maximum geometry. Separate DATA8 page and stack page have adjacent
PROT_NONE guards. RW/NX pages and RX/nonwritable root/candidate code permissions
are checked at both mapping endpoints. Full before/after maps must match.
No access-order hardware trace is captured.

Each observer saves16384 positive cases (2callers*128flags*8counts*8edgeinputs)
and640 negatives (5mutants*128flags). Inputs cover zero/max64/wrap/high-bit;
four target positions include aligned, unaligned and final-page qword.
Old targets vary and differ from the required nonzero-count final target;
count0 old words differ from x. Other GPRs and all pages vary deterministically.
128 requested AND observed profiles cover6 arithmetic bits and ID. Preserved
callee-saved registers, nonarithmetic flags, root return RSP and every byte
outside UNION(DATA8,private32) are checked against the endpoint contract.
RDI=target, RSI=x, RDX=n. A two-operand base256 carry oracle (with literal edge
checks, including full-width second operands) computes RAX=(x+n)mod2^64 and
DATA=old ifn0, otherwise(x+n-1)mod2^64 without replaying implementation loops.

Masks RESULT=1 DATA=2 STACK=4 SAVED=8 FLAGS=16 MEMORY=32 ROOT=64.
Owned safe mutant exact expectations: skip-iteration n3 mask3; no-store n3
mask2; stale-reload n1 mask1; outside-DATA n3 mask32; callee-saved n3 mask8.
Every mutant access stays in the owned mapped pages. Timeout/signal/IO/resource
and admission failures fail the gate; they never establish semantic rejection.
Records retain requested/full pre/post registers+flags and all four pages,
page/code/root/helper SHA256 and actual code/root/helper addresses. The binary
format is versioned, host-local little-endian, and native C struct-layout sized.
Read-only replay recomputes all page hashes/contracts and derives the complete
matrix from actual pre-RSI/RDX/RDI/effective flags. JSON is an indexed duplicate;
shell also checks its actual sequence, exact masks and completed coverage.
SCOPE

flags=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-stack-protector -fno-unwind-tables
    -fno-asynchronous-unwind-tables -fno-optimize-sibling-calls)
link_flags=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e caller -Ttext=0x401000)
observer_flags=(-std=gnu2x -O2 -Wall -Wextra -Werror -Wshadow -Wformat=2
    -Wstrict-prototypes '-Wa,--fatal-warnings' -fno-lto -fcf-protection=none -fPIE -pie
    '-Wl,--build-id=none,-z,noexecstack')
{
    printf 'compiler_flags='; printf '%q ' "${flags[@]}"; printf '\n'
    printf 'linker_flags='; printf '%q ' "${link_flags[@]}"; printf '\n'
    printf 'observer_flags='; printf '%q ' "${observer_flags[@]}"; printf '%s\n' '-lcrypto'
} > "$output/metadata/flags.txt"
artifact_metadata() {
    local artifact=$1
    run /usr/bin/readelf -aW "$artifact" > "$artifact.readelf.txt"
    run /usr/bin/objdump -drwC -Mintel --show-raw-insn "$artifact" > "$artifact.disasm.txt"
    run /usr/bin/objdump -s "$artifact" > "$artifact.sections-hex.txt"
    run /usr/bin/nm -n -S --defined-only "$artifact" > "$artifact.symbols.txt"
    run /usr/bin/file "$artifact" > "$artifact.file.txt"
}
phase_begin compilation
for compiler_name in gcc13 clang18; do
    if [[ $compiler_name == gcc13 ]]; then
        compiler=/usr/bin/gcc-13 length=45 helper_offset=38
    else
        compiler=/usr/bin/clang-18 length=52 helper_offset=45
    fi
    directory="$output/$compiler_name/separate-tu"
    observer="$output/observer-$compiler_name"
    mkdir -p "$directory" "$observer"
    run "$compiler" "${flags[@]}" -c fixtures/call-memory-loop64-caller.c -o "$directory/caller.o" \
        > "$directory/compile-caller.log" 2>&1
    run "$compiler" "${flags[@]}" -c fixtures/call-memory-loop64-helper.c -o "$directory/helper.o" \
        > "$directory/compile-helper.log" 2>&1
    run /usr/bin/ld "${link_flags[@]}" "$directory/caller.o" "$directory/helper.o" \
        -o "$directory/function.elf" > "$directory/link.log" 2>&1
    for artifact in "$directory/caller.o" "$directory/helper.o" "$directory/function.elf"; do
        artifact_metadata "$artifact"
    done
    run /usr/bin/readelf -rW "$directory/function.elf" > "$directory/final-relocations.txt"
    run grep -Fx 'There are no relocations in this file.' "$directory/final-relocations.txt" \
        > "$directory/relocation-check.txt"
    run /usr/bin/objdump -h "$directory/function.elf" > "$directory/final-sections.txt"
    elf_entry=$(run awk '/Entry point address:/ {print $NF}' "$directory/function.elf.readelf.txt")
    caller_address=$(run awk '$NF == "caller" {print "0x" $1}' "$directory/function.elf.symbols.txt")
    helper_address=$(run awk '$NF == "helper" {print "0x" $1}' "$directory/function.elf.symbols.txt")
    caller_size=$(run awk '$NF == "caller" {print "0x" $2}' "$directory/function.elf.symbols.txt")
    helper_size=$(run awk '$NF == "helper" {print "0x" $2}' "$directory/function.elf.symbols.txt")
    text_address=$(run awk '$2 == ".text" {print "0x" $4}' "$directory/final-sections.txt")
    text_size=$(run awk '$2 == ".text" {print "0x" $3}' "$directory/final-sections.txt")
    for number in "$elf_entry" "$caller_address" "$helper_address" "$caller_size" \
        "$helper_size" "$text_address" "$text_size"; do [[ $number =~ ^0x[[:xdigit:]]+$ ]]; done
    if (( elf_entry != caller_address || text_address != 0x401000 || text_size != length ||
        caller_address != text_address || helper_address-text_address != helper_offset ||
        caller_size != helper_offset || helper_size != 7 )); then
        echo 'Final ELF entry/symbol/whole-text binding differs from the supported profile' >&2
        exit 1
    fi
    printf 'profile=%s text=%s size=%d entry=%s caller=%s helper=%s entry_offset=0 helper_offset=%d caller_size=%d helper_size=7\n' \
        "$compiler_name" "$text_address" "$text_size" "$elf_entry" "$caller_address" "$helper_address" \
        "$helper_offset" "$caller_size" > "$directory/entry-binding.txt"
    run /usr/bin/objcopy --dump-section ".text=$directory/text.bin" "$directory/function.elf"
    [[ $(run stat -c %s "$directory/text.bin") == "$length" ]]
    run od -An -v -tx1 "$directory/text.bin" > "$directory/text.hex"
    run sha256sum "$directory/caller.o" "$directory/helper.o" "$directory/function.elf" \
        "$directory/text.bin" > "$directory/artifact-SHA256SUMS"
    texts+=("$directory/text.bin")
    run "$compiler" "${observer_flags[@]}" fixtures/call-memory-loop64-check.c \
        fixtures/call-memory-loop64-check.S -lcrypto -o "$observer/check.elf" > "$observer/build.log" 2>&1
    artifact_metadata "$observer/check.elf"
    run /usr/bin/ldd "$observer/check.elf" > "$observer/shared-libraries.txt"
    run awk '/=> \// {print $3} /^[[:space:]]*\// {print $1}' "$observer/shared-libraries.txt" \
        > "$observer/shared-library-paths.txt"
    while IFS= read -r library; do run sha256sum "$library"; done \
        < "$observer/shared-library-paths.txt" > "$observer/shared-library-SHA256SUMS"
done
run sha256sum "${texts[@]}" "$output/observer-gcc13/check.elf" "$output/observer-clang18/check.elf" \
    > "$output/native-input-SHA256SUMS"
phase_pass compilation

phase_begin authentication
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    run /usr/bin/objcopy --dump-section ".edsl_call_memory_loop64=$observer/embedded.bin" \
        --dump-section ".edsl_call_memory_loop64_mutants=$observer/owned-mutants.bin" "$observer/check.elf"
    run cat "${texts[@]}" > "$observer/compiled-whole-texts.bin"
    run cmp "$observer/compiled-whole-texts.bin" "$observer/embedded.bin"
    gcc_begin=$(run awk '$NF == "cm_gcc" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    gcc_end=$(run awk '$NF == "cm_gcc_end" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    clang_begin=$(run awk '$NF == "cm_clang" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    clang_end=$(run awk '$NF == "cm_clang_end" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    for number in "$gcc_begin" "$gcc_end" "$clang_begin" "$clang_end"; do [[ $number =~ ^0x[[:xdigit:]]+$ ]]; done
    (( gcc_end-gcc_begin == 45 && clang_begin == gcc_end && clang_end-clang_begin == 52 ))
    printf 'gcc_begin=%s gcc_end=%s gcc_length=45 clang_begin=%s clang_end=%s clang_length=52\n' \
        "$gcc_begin" "$gcc_end" "$clang_begin" "$clang_end" > "$observer/embedded-binding.txt"
done
phase_pass authentication

phase_begin rejections
printf '%s\n' 'Whole counted DATA8 text differs from embedded expected profiles' > "$output/rejection-diagnostic.txt"
printf '%s\n' 'Evidence directory must be an empty real directory' > "$output/admission-diagnostic.txt"
printf 'observer\tinput_profile\tmutation\texit\tstatus\n' > "$output/rejection-status.tsv"
printf 'observer\tguard\texit\tstatus\n' > "$output/guard-status.tsv"
expect_rejection() {
    local executable=$1 destination=$2 expected=$3 case_dir=$4 status=0
    shift 4
    run timeout -k 5s 20s "$executable" "$destination" "$@" \
        > "$case_dir/stdout.txt" 2> "$case_dir/stderr.txt" || status=$?
    printf '%d\n' "$status" > "$case_dir/exit-status.txt"
    if [[ $status != 2 || -s $case_dir/stdout.txt ]] ||
        ! run cmp "$expected" "$case_dir/stderr.txt"; then
        printf 'Exact rejection failed: %s exit=%d\n' "$case_dir" "$status" >&2
        exit 1
    fi
}
flip_byte() {
    local original=$1 destination=$2 position=$3 value octet
    run cp "$original" "$destination"
    value=$(run od -An -v -tu1 -j "$position" -N 1 "$original")
    printf -v octet '\\%03o' "$((value ^ 1))"
    printf '%b' "$octet" | run dd of="$destination" bs=1 seek="$position" count=1 conv=notrunc status=none
}
reject_input() {
    local observer=$1 index=$2 mutation=$3 case_dir=$4
    local inputs=("${texts[@]}")
    inputs[index]="$case_dir/input.bin"
    [[ ! -e $case_dir/no-probes ]]
    expect_rejection "$observer/check.elf" "$case_dir/no-probes" "$output/rejection-diagnostic.txt" "$case_dir" "${inputs[@]}"
    [[ ! -e $case_dir/no-probes ]]
    if [[ $mutation == flip-* || $mutation == truncated || $mutation == appended || $mutation == cross-profile ]]; then
        rejection_count=$((rejection_count+1))
        printf '%s\t%d\t%s\t2\tPASS\n' "${observer##*/}" "$index" "$mutation" >> "$output/rejection-status.tsv"
    else
        guard_count=$((guard_count+1))
        printf '%s\tinput%d-%s\t2\tPASS\n' "${observer##*/}" "$index" "$mutation" >> "$output/guard-status.tsv"
    fi
}
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    for index in 0 1; do
        original=${texts[index]}
        length=$(run stat -c %s "$original")
        for ((position=0; position<length; position++)); do
            case_dir="$observer/rejections/$index-flip-$position"
            mkdir -p "$case_dir"
            flip_byte "$original" "$case_dir/input.bin" "$position"
            reject_input "$observer" "$index" "flip-$position" "$case_dir"
        done
        for mutation in truncated appended cross-profile empty missing directory symlink fifo; do
            case_dir="$observer/rejections/$index-$mutation"
            mkdir -p "$case_dir"
            case $mutation in
                truncated) run head -c "$((length-1))" "$original" > "$case_dir/input.bin" ;;
                appended) run cat "$original" > "$case_dir/input.bin"; printf '\x00' >> "$case_dir/input.bin" ;;
                cross-profile) run cp "${texts[1-index]}" "$case_dir/input.bin" ;;
                empty) : > "$case_dir/input.bin" ;;
                missing) ;;
                directory) mkdir "$case_dir/input.bin" ;;
                symlink) run ln -s "$original" "$case_dir/input.bin" ;;
                fifo) run mkfifo "$case_dir/input.bin" ;;
            esac
            reject_input "$observer" "$index" "$mutation" "$case_dir"
        done
    done
    # Change first and last bytes of BOTH embedded slots. The files stay valid.
    # The modified executable is our known observer, never an unknown candidate.
    for position in 0 44 45 96; do
        case_dir="$observer/guards/embedded-$position"
        mkdir -p "$case_dir"
        flip_byte "$observer/embedded.bin" "$case_dir/embedded.bin" "$position"
        run /usr/bin/objcopy --update-section ".edsl_call_memory_loop64=$case_dir/embedded.bin" \
            "$observer/check.elf" "$case_dir/check.elf"
        expect_rejection "$case_dir/check.elf" "$case_dir/no-probes" "$output/rejection-diagnostic.txt" "$case_dir" "${texts[@]}"
        [[ ! -e $case_dir/no-probes ]]
        guard_count=$((guard_count+1))
        printf '%s\tembedded-%d\t2\tPASS\n' "${observer##*/}" "$position" >> "$output/guard-status.tsv"
    done
    for guard in nonempty symlink regular-file missing auth-before-output; do
        case_dir="$observer/guards/$guard"
        mkdir -p "$case_dir"
        inputs=("${texts[@]}")
        diagnostic="$output/admission-diagnostic.txt"
        case $guard in
            nonempty|auth-before-output)
                mkdir "$case_dir/destination"
                printf 'owned admission sentinel\n' > "$case_dir/expected"
                run cp "$case_dir/expected" "$case_dir/destination/sentinel"
                if [[ $guard == auth-before-output ]]; then
                    inputs[1]="$case_dir/missing.bin"
                    diagnostic="$output/rejection-diagnostic.txt"
                fi ;;
            symlink) mkdir "$case_dir/real-directory"; run ln -s "$case_dir/real-directory" "$case_dir/destination" ;;
            regular-file) printf 'owned admission sentinel\n' > "$case_dir/expected"; run cp "$case_dir/expected" "$case_dir/destination" ;;
            missing) ;;
        esac
        expect_rejection "$observer/check.elf" "$case_dir/destination" "$diagnostic" "$case_dir" "${inputs[@]}"
        case $guard in
            nonempty|auth-before-output)
                run cmp "$case_dir/expected" "$case_dir/destination/sentinel"
                [[ $(find "$case_dir/destination" -mindepth 1 -maxdepth 1 -type f | wc -l) == 1 ]] ;;
            symlink) [[ -z $(find "$case_dir/real-directory" -mindepth 1 -print -quit) ]] ;;
            regular-file) run cmp "$case_dir/expected" "$case_dir/destination" ;;
            missing) [[ ! -e $case_dir/destination ]] ;;
        esac
        guard_count=$((guard_count+1))
        printf '%s\t%s\t2\tPASS\n' "${observer##*/}" "$guard" >> "$output/guard-status.tsv"
    done
done
[[ $rejection_count == 206 && $guard_count == 38 ]]
[[ $(run awk 'END {print NR-1}' "$output/rejection-status.tsv") == 206 ]]
[[ $(run awk 'END {print NR-1}' "$output/guard-status.tsv") == 38 ]]
phase_pass rejections

phase_begin native
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    mkdir "$observer/positive"
    run timeout -k 5s 180s "$observer/check.elf" "$observer/positive" "${texts[@]}" \
        > "$observer/stdout.txt" 2> "$observer/results.txt"
    [[ ! -s $observer/stdout.txt ]]
    run grep -Fx 'native=PASS positive=16384 negative=640 flag_profiles=128 counts=8 inputs=8 maps_equal=true failures=0 formal=NOTRUN' \
        "$observer/results.txt" > "$observer/native-receipt-check.txt"
    run cmp "$observer/positive/maps-before.txt" "$observer/positive/maps-after.txt"
    cat "$observer/results.txt" >&2
done
phase_pass native

phase_begin replay
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    run timeout -k 5s 180s "$observer/check.elf" --verify "$observer/positive" "${texts[@]}" \
        > "$observer/replay-stdout.txt" 2> "$observer/replay-results.txt"
    [[ ! -s $observer/replay-stdout.txt ]]
    run grep -Fx 'replay=PASS positive=16384 negative=640 flag_profiles=128 counts=8 inputs=8 page_hashes=68096 exact_masks=true formal=NOTRUN' \
        "$observer/replay-results.txt" > "$observer/replay-receipt-check.txt"
done
phase_pass replay

phase_begin coverage
printf 'observer\tpositive\tnegative\tflag_profiles\tcounts\tinputs\tpage_size\tpage_bytes\tstatus\n' > "$output/native-status.tsv"
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    run /usr/bin/jq 'if (.pre|length)==16 and (.post|length)==16 and (.requested|length)==16 and
        (.sha256|length)==4 and .reached_root==true and (.failure_mask==.expected_mask)
        then empty else error("Incomplete or inconsistent JSON record") end' \
        "$observer/positive/observations.jsonl" > /dev/null
    # Independent shell count of completed JSON records; binary replay already
    # recomputes the contract and checks coverage against actual captured GPRs.
    run awk '
      function value(n, a) { split(fields[n],a,":"); gsub(/"/,"",a[2]); return a[2] }
      BEGIN {
        want["skip-iteration"]=3; want["no-store"]=2; want["stale-reload"]=1
        want["outside-DATA"]=32; want["callee-saved"]=8
        split("0 1 2 3 7 31 257 1024", ns, " ")
      }
      {
        if ($0 !~ /^\{"case":[0-9]+,/ || $0 !~ /"reached_root":true\}$/) exit 1
        split($0,fields,",")
        id=value(1); name=value(2); neg=value(3); f=value(4); c=value(5); s=value(6)
        n=value(7); offset=value(9); page=value(10); pageoff=value(11)
        mask=value(22); expected=value(23)
        if (id != NR-1 || f < 0 || f >= 128 || page < 4096 || page%8 ||
            pageoff != (NR-1)*page*4 || mask != expected || offset < 0 || offset > page-8) exit 1
        if (NR == 1) size=page
        if (page != size) exit 1
        if ((name=="gcc13" || name=="clang18") && neg=="false") {
          if (c < 0 || c >= 8 || s < 0 || s >= 8 || n != ns[c+1] || mask != 0 ||
              seen[name,f,c,s]++) exit 1
          pos++
        } else if (name in want && neg=="true") {
          if (n != (name=="stale-reload" ? 1 : 3) || mask != want[name] || seenbad[name,f]++) exit 1
          bad++
        } else exit 1
        completed[name,f]++
      }
      END {
        if (NR != 17024 || pos != 16384 || bad != 640) exit 1
        for (f=0; f<128; f++) {
          if (completed["gcc13",f] != 64 || completed["clang18",f] != 64) exit 1
          for (m in want) if (completed[m,f] != 1) exit 1
        }
        printf "%d %d 128 8 8 %d\n",pos,bad,size
      }' "$observer/positive/observations.jsonl" > "$observer/observation-counts.txt"
    read -r positives negatives flag_profiles observed_counts observed_inputs page_size < "$observer/observation-counts.txt"
    [[ $positives == 16384 && $negatives == 640 && $flag_profiles == 128 && $observed_counts == 8 && $observed_inputs == 8 ]]
    page_bytes=$(run stat -c %s "$observer/positive/pages.bin")
    (( page_bytes == (positives+negatives)*page_size*4 ))
    printf '%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\tPASS\n' "$compiler_name" "$positives" "$negatives" \
        "$flag_profiles" "$observed_counts" "$observed_inputs" "$page_size" "$page_bytes" >> "$output/native-status.tsv"
    observer_count=$((observer_count+1))
    positive_count=$((positive_count+positives))
    negative_count=$((negative_count+negatives))
done
phase_pass coverage

phase_begin source_stability
run sha256sum --check "$output/native-input-SHA256SUMS" > "$output/native-input-stability.txt"
for compiler_name in gcc13 clang18; do
    run sha256sum --check "$output/$compiler_name/separate-tu/artifact-SHA256SUMS" \
        > "$output/$compiler_name/separate-tu/artifact-stability.txt"
done
snapshot "$output/native-source-final"
run cmp "$output/native-source.SHA256SUMS" "$output/native-source-final.SHA256SUMS"
run cmp "$output/native-source.files.list0" "$output/native-source-final.files.list0"
run cmp "$output/native-source.tar" "$output/native-source-final.tar"
phase_pass source_stability
# EXIT closes result/status/manifest only after every required phase.
