#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
if [[ $# -ne 0 || $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'usage: verify-locked-add64-native.sh (Linux x86_64 / System V)' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
cache="$root/artifacts/locked-add64-native"
mkdir -p "$cache"
output=$(mktemp -d "$cache/run.XXXXXXXX")
printf 'LOCK XADD full64 native evidence: %s\n' "$output"
exec 3>&1 4>&2
exec > "$output/script.log" 2>&1
ulimit -c 0
phase=initialization
complete=0
record_command() { printf '%q ' "$@"; printf '\n'; }
run() {
    local code=0 started finished
    started=$(date -u +%FT%T.%NZ)
    record_command "$@" >> "$output/commands.txt"
    "$@" || code=$?
    finished=$(date -u +%FT%T.%NZ)
    printf '%s\t%s\t%s\t%s\n' "$phase" "$started" "$finished" "$code" >> "$output/exits.tsv"
    return "$code"
}
hash_evidence() {
    (cd "$output" && find . -type f ! -name EVIDENCE.sha256 -print0 | sort -z | xargs -0 sha256sum) \
        > "$output/EVIDENCE.sha256"
}
finish() {
    local code=$? manifest_code=0
    trap - EXIT
    set +e
    # Close the active log before hashing it; nothing hashed is changed afterward.
    exec 1>&3 2>&4
    if [[ $code -ne 0 || $complete -ne 1 ]]; then
        [[ $code -ne 0 ]] || code=1
        printf 'INCOMPLETE fixture/validation: exit=%s phase=%s; partial evidence retained; no defect claim\n' \
            "$code" "$phase" > "$output/result.txt"
    fi
    printf '%s\n' "$code" > "$output/script-status.txt"
    printf 'UTC=%s\nphase=%s\nexit=%s\n' "$(date -u +%FT%TZ)" "$phase" "$code" > "$output/terminal-status.txt"
    cat > "$output/RECEIPT.md" <<RECEIPT
Owned LOCK XADD native capture and actual-model runtime replay.
Exit: $code. Terminal phase: $phase. See result.txt, exits.tsv and commands.txt.
Source snapshots: source/; exact owned source manifest: OWNED-SOURCES.sha256.
Actual imported source closure: IMPORTED-SOURCES.sha256. Accepted provider
objects, paths and hashes: PROVIDER-OBJECTS.sha256, provider.txt, lean-lib/.
EVIDENCE.sha256 covers every regular evidence file including this receipt and
all partial logs; lean-lib/ contains only symlinks to the imported provider.
No universal proof, kernel replay of new observation theorems, physical TSO,
Linux correctness, source preservation/ordering, corpus or concurrency claim.
Only project-owned statically linked code executes. Crashes/unsupported profiles
are fixture/validation failures. No real security finding is claimed.
Lake may rebuild this checkout's model provider. No public source, CI/lake/import,
frozen input, baseline or git state is modified by this run.
RECEIPT
    hash_evidence && (cd "$output" && sha256sum --quiet --check EVIDENCE.sha256) || manifest_code=$?
    if [[ $manifest_code -ne 0 ]]; then
        code=1
        printf 'INCOMPLETE: manifest failure %s\n' "$manifest_code" > "$output/manifest-failure.txt"
        printf '1\n' > "$output/script-status.txt"
        hash_evidence
        (cd "$output" && sha256sum --quiet --check EVIDENCE.sha256)
    fi
    if [[ $code -eq 0 ]]; then
        printf 'PASS finite native/model conformance and 4 semantic corruption controls; closed manifest: %s\n' "$output"
    else
        printf 'INCOMPLETE fixture/validation (exit %s), retained evidence: %s\n' "$code" "$output" >&2
    fi
    exit "$code"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP
echo 'INCOMPLETE: native/model replay not finished' > "$output/result.txt"

phase=sources
owned=(tests/native/locked_add64/capture.h tests/native/locked_add64/capture.cpp
    tests/native/locked_add64/probe.S tests/LockedAdd64Native.lean scripts/verify-locked-add64-native.sh)
run sha256sum "${owned[@]}" > "$output/OWNED-SOURCES.sha256"
for file in "${owned[@]}" lean-toolchain; do
    run install -D -m 0644 "$file" "$output/source/$file"
done
run sha256sum lean-toolchain > "$output/TOOLCHAIN-SOURCE.sha256"
(cd "$output/source" && sha256sum --check "$output/OWNED-SOURCES.sha256" \
    && sha256sum --check "$output/TOOLCHAIN-SOURCE.sha256") > "$output/source-copy-check.txt"
run bash -n "$output/source/scripts/verify-locked-add64-native.sh"
run shellcheck -s bash "$output/source/scripts/verify-locked-add64-native.sh" > "$output/shellcheck.txt" 2>&1

phase=platform
run uname -srmo > "$output/platform.txt"
run hostname > "$output/hostname.txt"
run lscpu > "$output/cpu.txt"
run getconf GNU_LIBC_VERSION > "$output/libc.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
run cat /proc/self/status > "$output/process-status.txt"
for tool in clang++-18 objcopy objdump readelf shellcheck timeout bash sha256sum flock; do
    tool_path=$(command -v "$tool")
    printf '%s\t%s\n' "$tool" "$(realpath "$tool_path")" >> "$output/tool-paths.tsv"
    run sha256sum "$(realpath "$tool_path")" >> "$output/TOOLS.sha256"
    run "$tool" --version > "$output/tool-$tool.txt" 2>&1
done
run clang++-18 -dumpmachine > "$output/compiler-target.txt"

phase=compile_owned_fixture
run clang++-18 -std=gnu++2c -O2 -Wall -Wextra -Werror -fno-lto -fcf-protection=none \
    -fPIE -pie '-Wl,--build-id=none,-z,noexecstack' \
    "$output/source/tests/native/locked_add64/capture.cpp" \
    "$output/source/tests/native/locked_add64/probe.S" -o "$output/capture.elf" \
    > "$output/compile.txt" 2>&1
run objcopy --dump-section ".edsl_locked_add64=$output/instructions.bin" "$output/capture.elf"
run objdump -d -j .text -j .edsl_locked_add64 "$output/capture.elf" > "$output/disassembly.txt"
run readelf -h -l -S -s -r -n -W "$output/capture.elf" > "$output/elf.txt"

phase=native_matrix
run timeout --kill-after=2 30 "$output/capture.elf" "$output/instructions.bin" \
    > "$output/captures.tsv" 2> "$output/native-results.txt"
cat "$output/native-results.txt"
# Changed extraction is DATA and must be rejected before the first probe and
# before even the capture-format header is emitted.
run cp "$output/instructions.bin" "$output/altered-section.bin"
printf '\000' | run dd of="$output/altered-section.bin" bs=1 count=1 conv=notrunc status=none
code=0
run timeout --kill-after=2 10 "$output/capture.elf" "$output/altered-section.bin" \
    > "$output/altered-captures.tsv" 2> "$output/altered-results.txt" || code=$?
if [[ $code -ne 2 || -s "$output/altered-captures.tsv" ||
    $(< "$output/altered-results.txt") != 'Final ELF section extraction differs from executed bytes' ]]; then
    echo 'FAIL: exact executed-section identity negative control' >&2
    exit 1
fi

phase=build_model
# Lake checks this checkout's source/dependency traces even after a cache hit.
run flock /tmp/edsl-lean-build.lock lake build EDSL.X86.LockedAdd64 EDSL.Audit \
    > "$output/model-build.txt" 2>&1

phase=import_closure
# No broad cache overlay. Only the recursively ACTUAL project
# imports of the validator are linked into a private, complete module union.
# Standard Lean/Std imports come from the pinned toolchain's own sysroot.
provider="$root/.lake/build/lib/lean"
printf '%s\n' "$provider" > "$output/provider.txt"
declare -A imported=()
queue=(EDSL.X86.LockedAdd64 EDSL.Audit)
mkdir -p "$output/lean-lib"
for ((q=0; q<${#queue[@]}; q++)); do
    module=${queue[$q]}
    [[ -z ${imported[$module]:-} ]] || continue
    imported[$module]=1
    relative=${module//.//}
    source="$relative.lean"
    object="$provider/$relative.olean"
    [[ -f $source && -f $object ]] || { echo "Missing actual import: $module" >&2; exit 2; }
    run sha256sum "$source" >> "$output/IMPORTED-SOURCES.sha256"
    run install -D -m 0644 "$source" "$output/source/$source"
    run sha256sum "$object" >> "$output/PROVIDER-OBJECTS.sha256"
    mkdir -p "$output/lean-lib/$(dirname "$relative")"
    run ln -s "$object" "$output/lean-lib/$relative.olean"
    while IFS= read -r dependency; do
        queue+=("$dependency")
    done < <(awk '/^import / {for (i=2;i<=NF;i++) if ($i ~ /^EDSL[.]/) print $i}' "$source")
done
export LEAN_PATH="$output/lean-lib"
printf 'LEAN_NUM_THREADS=%s\nLEAN_PATH=%s\n' "$LEAN_NUM_THREADS" "$LEAN_PATH" > "$output/lean-environment.txt"

phase=pinned_lean
run flock /tmp/edsl-lean-build.lock lean --version > "$output/lean-version.txt"
[[ $(< "$output/lean-version.txt") == *'version 4.35.0'* ]] || { echo 'Unsupported Lean version' >&2; exit 2; }
run flock /tmp/edsl-lean-build.lock lean --print-prefix > "$output/lean-prefix.txt"
lean_prefix=$(< "$output/lean-prefix.txt")
run sha256sum "$lean_prefix/bin/lean" >> "$output/TOOLS.sha256"

phase=actual_step_runtime_replay
run timeout --kill-after=2 60 flock /tmp/edsl-lean-build.lock lean -DwarningAsError=true --run \
    "$output/source/tests/LockedAdd64Native.lean" "$output/captures.tsv" "$output/negative-controls" \
    > "$output/lean-replay.txt" 2>&1
cat "$output/lean-replay.txt"

phase=closing_bindings
run sha256sum --check "$output/OWNED-SOURCES.sha256" > "$output/owned-live-check.txt"
run sha256sum --check "$output/IMPORTED-SOURCES.sha256" > "$output/imported-live-check.txt"
run sha256sum --check "$output/PROVIDER-OBJECTS.sha256" > "$output/provider-live-check.txt"
(cd "$output/source" && sha256sum --check "$output/IMPORTED-SOURCES.sha256") > "$output/imported-copy-check.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite native conformance of project-owned full64 F0 REX.W 0F C1 /r instructions.
3072 CPU captures: 16 sources x 12 supported direct bases x both ignored-X
settings x eight value profiles. 192 source/base aliases and 192 RSP-source
captures are included. Aliases use the actual RAM address as delta; their wrap
profile starts at its additive inverse. Values cover complete high halves,
low32 carry, unsigned wrap/zero, both signed overflows, zero delta, AF/parity.
Actual CPU flags supply the expected defined ADD flags. C++ independently
checks unsigned modular arithmetic, full old response and neighboring qwords,
all outside-source GPRs, code/flags frames and the System V GPR/SP restoration.
All RF stores precede scratch use; only MOV/LEA precede post-flags capture, and
host RSP is restored before PUSHFQ. RFLAGS seed/capture precedes MOV setup while
host RSP is valid. Before GPRs are actual MOV captures, after RIP is a hardware
RIP-relative continuation label. Whole linked executable-section identity is
checked before any probe; changed extraction rejects without executing it.
RAM is aligned, within one cache line, owned ordinary user-stack WB storage.
Signals are blocked during the single-threaded matrix. No concurrent snapshot
global use, executable mappings of input data, private findings or stress test.
The Lean runtime parser replays actual public LockedAdd64.step, comparing every
captured GPR/full flags/qword/event, code and 24 data bytes. Permissions are
explicit replay-fixture assumptions, not physical PTE observations. Corrupted
qword high half, response high half, defined flag and opcode must reject at
their precise semantic gates. The dependency audit permits only propext,
Classical.choice and Quot.sound; observations remain runtime IO evidence.
Assumptions/limits: Linux x86-64 System V, long mode/four-level canonical user
addresses, CET/AC/TF/RF/NT/VM disabled, normal WB translation/alias behavior,
ordinary owned aligned RAM and no asynchronous interference. GNU++26 spelling
gnu++2c and -fcf-protection=none apply only to this synthetic owned fixture.
No new proved observation theorem, universal ISA/CPU/OS theorem, physical TSO,
Linux/source-language ordering or preservation, corpus or concurrency claim.
Failure, crash, timeout or unsupported profile is a fixture/validation failure.
Existing baseline 4/40, 8/80 and frozen concurrent fixtures are untouched.
SCOPE
echo 'PASS: 3072 finite native captures, actual LockedAdd64.step runtime replay, dependency audit, 4 semantic corruption controls, pre-probe extraction rejection' \
    > "$output/result.txt"
phase=complete
complete=1
