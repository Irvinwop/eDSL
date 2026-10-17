#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
umask 022
export LC_ALL=C TZ=UTC
native_only=false
if [[ $# == 1 && $1 == --native-only ]]; then
    native_only=true
elif [[ $# != 0 ]]; then
    echo 'usage: scripts/verify-call-memory64.sh [--native-only]' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Callable DATA8 native evidence requires Linux x86_64' >&2
    exit 2
fi
exec 9>/tmp/edsl-call-memory64-native-home.lock
if ! flock -n 9; then
    echo 'A callable DATA8 gate is already active; refusing duplicate work' >&2
    exit 2
fi
evidence_root=${CALL_MEMORY64_EVIDENCE_ROOT:-$PWD/.cache/call-memory64-native}
mkdir -p -- "$evidence_root"
evidence_root=$(realpath -- "$evidence_root")
if [[ $PWD == "$evidence_root" || $PWD == "$evidence_root/"* ]]; then
    echo 'The evidence root must not contain the source checkout' >&2
    exit 2
fi
output=$(mktemp -d "$evidence_root/run-$(date -u +%Y%m%dT%H%M%S)-XXXXXX")
printf 'Callable DATA8 evidence: %s\n' "$output" >&2
exec 3>"$output/commands.log" 4>"$output/command-status.tsv"
sequence=0
phases=(syntax snapshot toolchain compilation authentication rejections native formal source_stability)
declare -A phase_status
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
rejection_count=0
observer_count=0
positive_count=0
negative_count=0
flag_profile_count=0
overall=FAIL
run() {
    sequence=$((sequence + 1))
    local status=0 line arguments tag="$BASHPID.$sequence"
    printf -v arguments '%q ' "$@"
    printf -v line '[%s] cwd=%q argv=%s\n' "$tag" "$PWD" "$arguments"
    printf '%s' "$line" >&3
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
    if [[ ${phase_status[native]} == PASS ]]; then native=PASS;
    elif [[ ${phase_status[native]} == FAIL ]]; then native=FAIL; fi
    printf 'overall=%s native=%s formal=%s source_stability=%s native_only=%s observers=%d compiler_profiles=%d extraction_rejections=%d positive=%d negative=%d flag_profiles_per_observer=%d\n' \
        "$overall" "$native" "${phase_status[formal]}" "${phase_status[source_stability]}" \
        "$native_only" "$observer_count" "${#texts[@]}" "$rejection_count" \
        "$positive_count" "$negative_count" "$flag_profile_count" > "$output/result.txt"
    printf 'phase\tstatus\n' > "$output/phase-status.tsv"
    local phase
    for phase in "${phases[@]}"; do
        printf '%s\t%s\n' "$phase" "${phase_status[$phase]}" >> "$output/phase-status.tsv"
    done
    printf 'exit=%d UTC=%s native_only=%s\n' "$status" "$(date -u +%FT%TZ)" "$native_only" \
        > "$output/terminal-status.txt"
}
manifest() {
    (
        cd "$output" || exit 1
        # These two root files are excluded; nested formal manifests are inputs.
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
        if [[ ${phase_status[$phase]} != PASS ]]; then
            if [[ $phase != formal || $native_only != true || ${phase_status[$phase]} != NOTRUN ]]; then
                if [[ $status == 0 ]]; then status=1; fi
            fi
        fi
    done
    if [[ $status == 0 ]]; then overall=PASS; fi
    write_terminal "$status" || { status=1; overall=FAIL; }
    exec 3>&- 4>&-
    if ! manifest; then
        status=1
        overall=FAIL
        write_terminal "$status"
        manifest
    fi
    if [[ $status == 0 ]]; then cat "$output/result.txt" >&2;
    else printf 'Callable DATA8 gate FAIL; see %s\n' "$output" >&2; fi
    exit "$status"
}
texts=()
trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

phase_begin syntax
run bash -n scripts/verify-call-memory64.sh scripts/check-call-memory64-proofs.sh
run /usr/bin/shellcheck -s bash scripts/verify-call-memory64.sh \
    scripts/check-call-memory64-proofs.sh > "$output/shellcheck.txt" 2>&1
phase_pass syntax

# git supplies tracked AND public untracked inputs. Ignored data and the selected
# evidence root are excluded. NUL lists also support spaces/newlines in names.
# Canonical tar metadata makes the final comparison sensitive to contents, file
# names, symlink targets and executable modes, without timestamp-only failures.
public_snapshot() {
    local prefix=$1 source
    run git ls-files --cached --others --exclude-standard -z -- . > "$prefix.git-files.list0"
    : > "$prefix.files.list0"
    while IFS= read -r -d '' source; do
        if [[ $PWD/$source != "$evidence_root/"* ]]; then
            if [[ ! -f $source && ! -L $source ]]; then
                printf 'Public source is missing or unsupported: %q\n' "$source" >&2
                return 1
            fi
            printf '%s\0' "$source" >> "$prefix.files.list0"
        fi
    done < "$prefix.git-files.list0"
    run sort -zu -o "$prefix.files.list0" "$prefix.files.list0"
    if [[ ! -s $prefix.files.list0 ]]; then echo 'Empty public source snapshot' >&2; return 1; fi
    run tar --format=gnu --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
        --null --verbatim-files-from --no-recursion -T "$prefix.files.list0" -cf "$prefix.tar"
    run sha256sum -- "$prefix.tar" > "$prefix.SHA256SUMS"
}
phase_begin snapshot
mkdir -p "$output/metadata"
public_snapshot "$output/public-source"
run git rev-parse HEAD > "$output/metadata/git-head.txt"
run git status --short --untracked-files=all > "$output/metadata/git-status.txt"
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
    for tool in ld as readelf objcopy objdump nm file shellcheck; do run "/usr/bin/$tool" --version; done
    run /usr/bin/openssl version -a
    run /usr/bin/readlink -f /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as
} > "$output/metadata/platform-tools.txt" 2>&1
gcc_version=$(run /usr/bin/gcc-13 -dumpfullversion)
clang_version=$(run /usr/bin/clang-18 --version)
[[ $gcc_version == 13.* && $clang_version == *'clang version 18.'* ]]
run sha256sum /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as \
    /usr/bin/readelf /usr/bin/objcopy /usr/bin/objdump /usr/bin/nm /usr/bin/file \
    /usr/bin/shellcheck /usr/bin/openssl > "$output/metadata/tool-SHA256SUMS"
phase_pass toolchain

cat > "$output/scope.txt" <<'SCOPE'
Two complete actual separately compiled GNU23 texts: GCC13 and Clang18, each
18 bytes, caller/ELF entry offset0, helper offset11, linked text at0x401000.
The compiler and linker options are unchanged from verify-call-stack.sh; there
is no historical probe dependency or flag tuning. Full ELF and objects are
provenance. The generated Lean claims bind only the complete raw text and entry;
they do not certify the ELF loader or introduce a full-ELF artifact contract.

Each independently compiled PIE observer authenticates BOTH complete input data
files and both embedded end-label-bounded 18-byte slots before creating output
or probing. Only authenticated embedded text and four project-owned safe
mutants execute. Every byte position of each input, truncation, append and
cross-profile substitution must reject: exit2, exact diagnostic, empty stdout,
and no evidence directory created. Signals and timeouts fail the gate.

Native evidence consists of endpoint observations on ordinary Linux x86-64
user RAM, SysV, AC/DF clear, disabled CET and no asynchronous interference.
Unavailable CET hardware status is recorded and does not prove CET support.
The root entry uses JMP at RSP=S with an installed root return address. Actual
internal CALL/RET instructions use RAM. Private stack=[S-16,S), DATA8 is on a
separate guarded page. Each RW/NX page has two PROT_NONE guards. Captures retain
full pre/post stack and DATA pages, all16 GPRs, requested/effective flags, actual
root/entry/helper addresses and return RSP. Target old contents vary; target
pointers cover aligned, unaligned and last-qword positions. Unaligned machine
inputs make no C semantics claim. The independent base256 carry oracle checks
RAX=x+1 modulo2^64; DATA=x, callee-saved registers, nonarithmetic flags, root
return, whole pages outside the private-stack UNION DATA8, and endpoint mapping
permissions are checked. No access-order hardware trace is captured.

The native case totals and 128 flag profiles are verified from completed
evidence per observer; expected coverage is8192 positive and512 owned negative.
Native register/flag/page records are separate from the formal eight-instruction
execution and read trace. Default formal checking imports the client Covered
and Audit modules, instantiates both universal closed Claims on freshly
extracted byte list literals, audits dependencies, and replays the generated
module and transitive proofs in a fresh kernel. Explicit --native-only leaves
formal=NOTRUN. No C source-preservation theorem, Linux kernel theorem, new
grader/task/CLI or proof packet serialization is claimed or used.
SCOPE

# Exactly the old runner's compiler/linker options. No tuning for this target.
flags=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-stack-protector -fno-unwind-tables
    -fno-asynchronous-unwind-tables -fno-optimize-sibling-calls)
link_flags=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e caller -Ttext=0x401000)
observer_flags=(-std=gnu2x -O2 -Wall -Wextra -Werror -Wshadow -Wformat=2
    -Wstrict-prototypes -fno-lto -fcf-protection=none -fPIE -pie
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
    if [[ $compiler_name == gcc13 ]]; then compiler=/usr/bin/gcc-13; else compiler=/usr/bin/clang-18; fi
    directory="$output/$compiler_name/separate-tu"
    observer="$output/observer-$compiler_name"
    mkdir -p "$directory" "$observer"
    run "$compiler" "${flags[@]}" -c fixtures/call-memory64-caller.c -o "$directory/caller.o" \
        > "$directory/compile-caller.log" 2>&1
    run "$compiler" "${flags[@]}" -c fixtures/call-memory64-helper.c -o "$directory/helper.o" \
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
        "$helper_size" "$text_address" "$text_size"; do
        [[ $number =~ ^0x[[:xdigit:]]+$ ]]
    done
    if (( elf_entry != caller_address || text_address != 0x401000 || text_size != 18 ||
        caller_address != text_address || helper_address - text_address != 11 ||
        caller_size != 11 || helper_size != 7 )); then
        echo 'Final ELF entry/symbol/whole-text binding differs from the supported profile' >&2
        exit 1
    fi
    printf 'profile=%s text=%s size=%d entry=%s caller=%s helper=%s entry_offset=0 helper_offset=11 caller_size=11 helper_size=7\n' \
        "$compiler_name" "$text_address" "$text_size" "$elf_entry" "$caller_address" "$helper_address" \
        > "$directory/entry-binding.txt"
    run /usr/bin/objcopy --dump-section ".text=$directory/text.bin" "$directory/function.elf"
    [[ $(run stat -c %s "$directory/text.bin") == 18 ]]
    run od -An -v -tx1 "$directory/text.bin" > "$directory/text.hex"
    run sha256sum "$directory/caller.o" "$directory/helper.o" "$directory/function.elf" \
        "$directory/text.bin" > "$directory/artifact-SHA256SUMS"
    texts+=("$directory/text.bin")
    run "$compiler" "${observer_flags[@]}" fixtures/call-memory64-check.c \
        fixtures/call-memory64-check.S -lcrypto -o "$observer/check.elf" > "$observer/build.log" 2>&1
    artifact_metadata "$observer/check.elf"
    run /usr/bin/ldd "$observer/check.elf" > "$observer/shared-libraries.txt"
done
phase_pass compilation

phase_begin authentication
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    run /usr/bin/objcopy --dump-section ".edsl_call_memory=$observer/embedded.bin" \
        --dump-section ".edsl_call_memory_mutants=$observer/owned-mutants.bin" "$observer/check.elf"
    run cat "${texts[@]}" > "$observer/compiled-whole-texts.bin"
    run cmp "$observer/compiled-whole-texts.bin" "$observer/embedded.bin"
    gcc_begin=$(run awk '$NF == "cm_gcc" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    gcc_end=$(run awk '$NF == "cm_gcc_end" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    clang_begin=$(run awk '$NF == "cm_clang" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    clang_end=$(run awk '$NF == "cm_clang_end" {print "0x" $1}' "$observer/check.elf.symbols.txt")
    for number in "$gcc_begin" "$gcc_end" "$clang_begin" "$clang_end"; do
        [[ $number =~ ^0x[[:xdigit:]]+$ ]]
    done
    (( gcc_end - gcc_begin == 18 && clang_begin == gcc_end && clang_end - clang_begin == 18 ))
    printf 'gcc_begin=%s gcc_end=%s clang_begin=%s clang_end=%s slot_bytes=18\n' \
        "$gcc_begin" "$gcc_end" "$clang_begin" "$clang_end" > "$observer/embedded-binding.txt"
done
phase_pass authentication

phase_begin rejections
printf '%s\n' 'Whole callable DATA8 text differs from embedded expected profiles' > "$output/rejection-diagnostic.txt"
printf 'observer\tinput_profile\tmutation\texit\tstatus\n' > "$output/rejection-status.tsv"
reject_input() {
    local observer=$1 index=$2 mutation=$3 case_dir=$4 status=0
    local inputs=("${texts[@]}")
    inputs[index]="$case_dir/input.bin"
    # Leave this directory nonexistent: a rejected input must not create it.
    [[ ! -e $case_dir/no-probes ]]
    run timeout -k 5s 20s "$observer/check.elf" "$case_dir/no-probes" "${inputs[@]}" \
        > "$case_dir/stdout.txt" 2> "$case_dir/stderr.txt" || status=$?
    printf '%d\n' "$status" > "$case_dir/exit-status.txt"
    if [[ $status != 2 || -s $case_dir/stdout.txt || -e $case_dir/no-probes ]] ||
        ! run cmp "$output/rejection-diagnostic.txt" "$case_dir/stderr.txt"; then
        printf 'Pre-capture rejection failed: %s profile=%d mutation=%s exit=%d\n' \
            "$observer" "$index" "$mutation" "$status" >&2
        exit 1
    fi
    rejection_count=$((rejection_count + 1))
    printf '%s\t%d\t%s\t%d\tPASS\n' "${observer##*/}" "$index" "$mutation" "$status" \
        >> "$output/rejection-status.tsv"
}
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    for index in 0 1; do
        original=${texts[index]}
        length=$(run stat -c %s "$original")
        for ((position=0; position<length; position++)); do
            case_dir="$observer/rejections/$index-flip-$position"
            mkdir -p "$case_dir"
            run cp "$original" "$case_dir/input.bin"
            value=$(run od -An -v -tu1 -j "$position" -N 1 "$original")
            printf -v octet '\\%03o' "$((value ^ 1))"
            printf '%b' "$octet" | run dd of="$case_dir/input.bin" bs=1 seek="$position" \
                count=1 conv=notrunc status=none
            reject_input "$observer" "$index" "flip-$position" "$case_dir"
        done
        for mutation in truncated appended cross-profile; do
            case_dir="$observer/rejections/$index-$mutation"
            mkdir -p "$case_dir"
            case $mutation in
                truncated) run head -c "$((length - 1))" "$original" > "$case_dir/input.bin" ;;
                appended) run cat "$original" > "$case_dir/input.bin"; printf '\x00' >> "$case_dir/input.bin" ;;
                cross-profile) run cp "${texts[1-index]}" "$case_dir/input.bin" ;;
            esac
            reject_input "$observer" "$index" "$mutation" "$case_dir"
        done
    done
done
phase_pass rejections

phase_begin native
printf 'observer\tpositive\tnegative\tflag_profiles\tpage_size\tpage_bytes\tstatus\n' > "$output/native-status.tsv"
for compiler_name in gcc13 clang18; do
    observer="$output/observer-$compiler_name"
    mkdir "$observer/positive"
    run timeout -k 5s 180s "$observer/check.elf" "$observer/positive" "${texts[@]}" \
        > "$observer/stdout.txt" 2> "$observer/results.txt"
    [[ ! -s $observer/stdout.txt ]]
    summary=$(run cat "$observer/results.txt")
    if [[ ! $summary =~ ^native=PASS\ positive=([0-9]+)\ negative=([0-9]+)\ flag_profiles=([0-9]+)\ maps_equal=true\ failures=0\ formal=NOTRUN$ ]]; then
        echo 'Missing complete native success receipt' >&2
        exit 1
    fi
    positives=${BASH_REMATCH[1]} negatives=${BASH_REMATCH[2]} flag_profiles=${BASH_REMATCH[3]}
    [[ $positives == 8192 && $negatives == 512 && $flag_profiles == 128 ]]
    # Count actual saved cases by implementation and flag profile. This checks
    # completeness independently of the observer's summary counters.
    run awk '
      {
        if ($0 !~ /^\{"case":[0-9]+,/ || $0 !~ /"reached_root":true\}$/) exit 1
        split($0, fields, ",")
        split(fields[1], id, ":"); if (id[2] != NR-1) exit 1
        split(fields[2], name, ":"); split(fields[3], neg, ":")
        split(fields[4], flag, ":"); split(fields[6], page, ":")
        split(fields[7], offset, ":")
        if (flag[2] < 0 || flag[2] >= 128 || page[2] < 4096 || page[2] % 8 ||
            offset[2] != (NR-1)*page[2]*4) exit 1
        if (NR == 1) size=page[2]; if (page[2] != size) exit 1
        if ((name[2] == "\"gcc13\"" || name[2] == "\"clang18\"") && neg[2] == "false") pos++
        else if ((name[2] == "\"no-store\"" || name[2] == "\"stale-reload\"" ||
                  name[2] == "\"outside-target\"" || name[2] == "\"callee-saved\"") && neg[2] == "true") bad++
        else exit 1
        counts[name[2],flag[2]]++
      }
      END {
        if (NR != 8704 || pos != 8192 || bad != 512) exit 1
        for (f=0; f<128; f++) {
          if (counts["\"gcc13\"",f] != 32 || counts["\"clang18\"",f] != 32 ||
              counts["\"no-store\"",f] != 1 || counts["\"stale-reload\"",f] != 1 ||
              counts["\"outside-target\"",f] != 1 || counts["\"callee-saved\"",f] != 1) exit 1
        }
        printf "%d %d %d %d\n", pos,bad,128,size
      }' "$observer/positive/observations.jsonl" > "$observer/observation-counts.txt"
    read -r observed_positive observed_negative observed_flags page_size < "$observer/observation-counts.txt"
    [[ $observed_positive == "$positives" && $observed_negative == "$negatives" && $observed_flags == "$flag_profiles" ]]
    page_bytes=$(run stat -c %s "$observer/positive/pages.bin")
    (( page_bytes == (positives + negatives) * page_size * 4 ))
    run cmp "$observer/positive/maps-before.txt" "$observer/positive/maps-after.txt"
    printf '%s\t%d\t%d\t%d\t%d\t%d\tPASS\n' "$compiler_name" "$positives" "$negatives" \
        "$flag_profiles" "$page_size" "$page_bytes" >> "$output/native-status.tsv"
    observer_count=$((observer_count + 1))
    positive_count=$((positive_count + positives))
    negative_count=$((negative_count + negatives))
    if [[ $flag_profile_count != 0 && $flag_profile_count != "$flag_profiles" ]]; then
        echo 'Observers completed different flag profile coverage' >&2
        exit 1
    fi
    flag_profile_count=$flag_profiles
    cat "$observer/results.txt" >&2
done
phase_pass native

if ! $native_only; then
    phase_begin formal
    # The helper owns the single Lean lock; native work never holds it.
    run bash scripts/check-call-memory64-proofs.sh "$output/formal" "${texts[@]}"
    run grep -Fx 'formal=PASS whole_texts=2 universal_closed_claims=true mixed_cpu_os_execution=true union_ram_frame=true fresh_kernel=true' \
        "$output/formal/result.txt" > "$output/formal-receipt-check.txt"
    phase_pass formal
fi

phase_begin source_stability
public_snapshot "$output/public-source-final"
run cmp "$output/public-source.files.list0" "$output/public-source-final.files.list0"
run cmp "$output/public-source.tar" "$output/public-source-final.tar"
phase_pass source_stability
# Only the EXIT trap emits the overall result, after finalizing the manifest.
