#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
umask 022
export LC_ALL=C TZ=UTC
native_only=false
if [[ $# == 1 && $1 == --native-only ]]; then
    native_only=true
elif [[ $# != 0 ]]; then
    echo 'usage: scripts/verify-call-memory-loop64.sh [--native-only]' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec 9>/tmp/edsl-call-memory-loop64-master.lock
if ! flock -n 9; then
    echo 'A counted DATA8 combined gate is already active' >&2
    exit 2
fi
evidence_root=${CALL_MEMORY_LOOP64_EVIDENCE_ROOT:-$PWD/.cache/call-memory-loop64-combined}
mkdir -p -- "$evidence_root"
evidence_root=$(realpath -- "$evidence_root")
if [[ $PWD == "$evidence_root" || $PWD == "$evidence_root/"* ]]; then
    echo 'The evidence root must not contain the source checkout' >&2
    exit 2
fi
output=$(mktemp -d "$evidence_root/run-$(date -u +%Y%m%dT%H%M%S)-XXXXXX")
printf 'Counted DATA8 combined evidence: %s\n' "$output" >&2
exec 3>"$output/commands.log" 4>"$output/command-status.tsv"
sequence=0
overall=FAIL
phases=(syntax snapshot native formal source_stability)
declare -A phase_status
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
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
    local status=$1 phase
    printf 'overall=%s native=%s formal=%s source_stability=%s native_only=%s\n' \
        "$overall" "${phase_status[native]}" "${phase_status[formal]}" \
        "${phase_status[source_stability]}" "$native_only" > "$output/result.txt"
    printf 'phase\tstatus\n' > "$output/phase-status.tsv"
    for phase in "${phases[@]}"; do
        printf '%s\t%s\n' "$phase" "${phase_status[$phase]}" >> "$output/phase-status.tsv"
    done
    printf 'exit=%d UTC=%s native_only=%s\n' "$status" "$(date -u +%FT%TZ)" "$native_only" \
        > "$output/terminal-status.txt"
}
manifest() {
    (
        cd "$output" || exit 1
        # Materialize the list so enumeration failures cannot be hidden.
        # shellcheck disable=SC2094
        find . -type f ! -path ./SHA256SUMS ! -path ./MANIFEST-SHA256.txt \
            ! -path ./manifest-inputs.list0 -print0 | sort -z > manifest-inputs.list0 || exit 1
        xargs -0 -r sha256sum -- < manifest-inputs.list0 > SHA256SUMS || exit 1
        sha256sum manifest-inputs.list0 >> SHA256SUMS || exit 1
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
        status=1; overall=FAIL
        write_terminal "$status"
        manifest
    fi
    cat "$output/result.txt" >&2
    exit "$status"
}
trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

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
    [[ -s $prefix.files.list0 ]]
    run tar --format=gnu --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
        --null --verbatim-files-from --no-recursion -T "$prefix.files.list0" -cf "$prefix.tar"
    run sha256sum -- "$prefix.tar" > "$prefix.SHA256SUMS"
}

phase_begin syntax
run bash -n scripts/verify-call-memory-loop64.sh scripts/verify-call-memory-loop64-native.sh \
    scripts/check-call-memory-loop64-proofs.sh
run shellcheck -s bash scripts/verify-call-memory-loop64.sh scripts/verify-call-memory-loop64-native.sh \
    scripts/check-call-memory-loop64-proofs.sh > "$output/shellcheck.txt" 2>&1
phase_pass syntax

phase_begin snapshot
mkdir "$output/metadata"
run git rev-parse HEAD > "$output/metadata/git-head.txt"
run git status --short --untracked-files=all > "$output/metadata/git-status.txt"
public_snapshot "$output/public-source"
cat > "$output/scope.txt" <<'SCOPE'
Native observations and formal correctness are distinct phases. The child
native gate recompiles both separately linked owned GNU23 profiles, authenticates
complete text before execution/output and retains bounded native observations.
The formal phase independently binds the complete extracted raw bytes and entry
zero to the universal callable contract, audits dependencies and replays in a
fresh kernel. Native observation records are never proof premises. Full ELF is
link/extraction provenance; no new ELF-loader or process-startup theorem is claimed.
Default checking includes formal verification. Explicit --native-only reports
formal=NOTRUN. Instruction costs are separate model results, without hardware
cycle or micro-op claims. Ordinary sequential RAM, four-level canonical addresses,
AC/CET-disabled execution and no asynchronous interference remain material
physical correspondence assumptions. There is no source/IR or kernel refinement,
concurrency, atomic, syscall, indirect-call or recursion claim from this slice.
The final snapshot checks all public source bytes, paths, symlink targets and
executable modes throughout this combined run. No new grader CLI is used.
SCOPE
phase_pass snapshot

phase_begin native
run bash scripts/verify-call-memory-loop64-native.sh "$output/native" > "$output/native.log" 2>&1
run grep -E '^overall=PASS native=PASS formal=NOTRUN native_only=true ' "$output/native/result.txt" \
    > "$output/native-receipt.txt"
phase_pass native

if ! $native_only; then
    phase_begin formal
    # The proof helper owns its Lean lock; do not hold it around this call.
    run bash scripts/check-call-memory-loop64-proofs.sh "$output/formal" \
        "$output/native/gcc13/separate-tu/text.bin" "$output/native/clang18/separate-tu/text.bin" \
        > "$output/formal.log" 2>&1
    run grep -Fx 'formal=PASS whole_texts=2 universal_closed_claims=true mixed_cpu_os_execution=true union_ram_frame=true fresh_kernel=true' \
        "$output/formal/result.txt" > "$output/formal-receipt.txt"
    phase_pass formal
fi

phase_begin source_stability
public_snapshot "$output/public-source-final"
run cmp "$output/public-source.files.list0" "$output/public-source-final.files.list0"
run cmp "$output/public-source.tar" "$output/public-source-final.tar"
phase_pass source_stability
