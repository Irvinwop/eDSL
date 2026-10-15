#!/usr/bin/env bash
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Mutex native integration requires Linux x86_64' >&2
    exit 2
fi
# verify-compilers.sh produces the owned artifacts. Re-certify their exact raw
# bytes here before execution, using the existing certificate paths: these are
# reused artifact profiles, not additional distinct compiler-output certificates.
output=artifacts/mutex-fixtures
mkdir -p "$output"
lake build edsl-certify
certifier=.lake/build/bin/edsl-certify
compiler=${EDSL_CLANG:-clang}
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread
           fixtures/mutex-check.c -o "$output/native-check")
printf '%q ' "$compiler" "${arguments[@]}" > "$output/arguments.txt"
printf '\n' >> "$output/arguments.txt"
"$compiler" --version > "$output/compiler.txt"
"$compiler" "${arguments[@]}"
for mode in clang-c clang-cpp gcc-c; do
    directory="$output/$mode"
    mkdir -p "$directory"
    for profile in exchange32 load32 store32; do
        source="artifacts/compiler-fixtures/$mode-$profile"
        if [[ ! -f "$source/function.bin" ]]; then
            echo "Missing owned fixture $source/function.bin; first run scripts/verify-compilers.sh" >&2
            exit 2
        fi
        lake env "$certifier" "$profile" "$source/function.bin" "$source/Certificate.lean"
    done
    timeout 30 "$output/native-check" "artifacts/compiler-fixtures/$mode-exchange32/function.bin" \
        "artifacts/compiler-fixtures/$mode-load32/function.bin" \
        "artifacts/compiler-fixtures/$mode-store32/function.bin" > "$directory/native.txt"
    sha256sum fixtures/mutex-check.c "$output/native-check" \
        "artifacts/compiler-fixtures/$mode-exchange32/function.bin" \
        "artifacts/compiler-fixtures/$mode-load32/function.bin" \
        "artifacts/compiler-fixtures/$mode-store32/function.bin" > "$directory/SHA256SUMS"
    echo "Re-certified exchange/load/store bytes and observed protected-payload workloads ($mode)"
done

# Owned safe semantic mutant: load ESI instead of storing it. The independent
# protected-payload total must detect this even though mutual exclusion remains.
mkdir -p "$output/rejections"
printf '\x8b\x37\xc3' > "$output/rejections/no-store.bin"
status=0
lake env "$certifier" store32 "$output/rejections/no-store.bin" "$output/rejections/Rejected.lean" \
    > "$output/rejections/certificate.log" 2>&1 || status=$?
if [[ $status -ne 3 ]]; then
    cat "$output/rejections/certificate.log"
    echo "Expected unsupported store rejection 3, got $status" >&2
    exit 1
fi
status=0
timeout 30 "$output/native-check" artifacts/compiler-fixtures/clang-c-exchange32/function.bin \
    artifacts/compiler-fixtures/clang-c-load32/function.bin "$output/rejections/no-store.bin" \
    > "$output/rejections/native.log" 2>&1 || status=$?
if [[ $status -ne 1 ]]; then
    cat "$output/rejections/native.log"
    echo "Expected independent native payload rejection 1, got $status" >&2
    exit 1
fi
echo 'Owned no-store mutant remains unverified and fails independent native payload observations'
