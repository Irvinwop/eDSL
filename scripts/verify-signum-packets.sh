#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-signum-packets.sh' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export EDSL_REGISTERED_PACKET_OUTPUT=${EDSL_SIGNUM_OUTPUT:-artifacts/signum-packets}
exec bash scripts/verify-registered-packets.sh signumSigned32 tests.GradingSignum \
    EDSL.Tests.GradingSignum 11648 17 4880 15
