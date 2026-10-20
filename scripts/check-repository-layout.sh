#!/usr/bin/env bash
set -euo pipefail

repository_root=$(git -C "$(dirname -- "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)

# NUL-delimited paths preserve whitespace and other special filename characters.
# Keep Git's failure status as well as the checker status through pipefail.
git -C "$repository_root" ls-files --cached -z -- '*.lean' | (
    failed=0
    while IFS= read -r -d '' path; do
        case "$path" in
            */* | EDSL.lean | lakefile.lean) ;;
            *.lean)
                printf 'Unexpected tracked Lean source at repository root: %q\n' "$path" >&2
                failed=1
                ;;
        esac
    done
    if (( failed )); then
        printf 'Only EDSL.lean and lakefile.lean belong at root; place command entrypoints under Tools/.\n' >&2
        exit 1
    fi
)

printf 'Repository layout check passed.\n'
