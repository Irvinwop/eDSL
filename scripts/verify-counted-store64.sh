#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
bash scripts/verify-counted-store64-native.sh
output=artifacts/counted-store64-native
flock /tmp/edsl-lean-build.lock lake build edsl-certify-counted-store64
certifier=(lake env .lake/build/bin/edsl-certify-counted-store64)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected counted-store status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
expect_status 0 raw "${certifier[@]}" "$output/function.bin" "$output/Raw.lean"
expect_status 0 elf "${certifier[@]}" --elf "$output/function.elf" "$output/ELF.lean"
mkdir -p "$output/rejections"
printf '\110\211\360\303' > "$output/rejections/missing-loop.bin"
printf '\211\322' > "$output/rejections/narrow-count.bin"
cat "$output/function.bin" >> "$output/rejections/narrow-count.bin"
head -c 19 "$output/function.bin" > "$output/rejections/truncated.bin"
cp "$output/function.bin" "$output/rejections/trailing.bin"
printf '\220' >> "$output/rejections/trailing.bin"
for name in missing-loop narrow-count truncated trailing; do
    expect_status 3 "rejections/$name" "${certifier[@]}" "$output/rejections/$name.bin" \
        "$output/rejections/$name.lean"
done
: > "$output/rejections/empty.bin"
printf '\177ELF' > "$output/rejections/short.elf"
expect_status 4 rejections/empty "${certifier[@]}" "$output/rejections/empty.bin" "$output/rejections/empty.lean"
expect_status 4 rejections/short "${certifier[@]}" --elf "$output/rejections/short.elf" "$output/rejections/short.lean"
expect_status 2 rejections/usage "${certifier[@]}"
expect_status 5 rejections/io "${certifier[@]}" "$output/rejections/not-present.bin" "$output/rejections/io.lean"
cat > "$output/proof-scope.txt" <<'SCOPE'
Both generated files kernel-check literal artifact binding, all-full64-count
termination, the independent modular result, zero-count target retention,
outside8/permission/ABI/nonarithmetic-flag frames, actual RET, and current-world
owner mutations with usable returned authority. The ELF file additionally binds
the parsed restricted container, loaded entry code and explicit caller facts.
Fuel is conservatively bounded by 7*(count.toNat+2), including RET. This is not
an exact instruction count, store-count, source-preservation or optimality claim.
This one exact GCC profile is separate from the fixed-contract grader registry;
different byte shapes remain unsupported. Native evidence has its own scope.txt.
SCOPE
{
    sha256sum fixtures/counted-store64.c fixtures/counted-store64-check.c \
        fixtures/cfg/trampoline.S scripts/verify-counted-store64-native.sh \
        scripts/verify-counted-store64.sh CountedStore64Main.lean \
        EDSL/CountedStore64/*.lean EDSL/Grading/Trace/ResourceCutpoints.lean \
        lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Counted-store raw/ELF proofs, native contract and owned-mutant checks passed'
