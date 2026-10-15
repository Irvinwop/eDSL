#!/usr/bin/env bash
set -euo pipefail

lake env lean -DwarningAsError=true scripts/Audit.lean

# A theorem inside the project depends on an axiom outside the namespace.
# The audit must follow that dependency and reject it for the right reason.
negative_source=$(mktemp /tmp/edsl-audit-negative.XXXXXX.lean)
negative_log=$(mktemp /tmp/edsl-audit-negative.XXXXXX.log)
trap 'unlink "$negative_source"; unlink "$negative_log"' EXIT
awk '/^run_cmd do/ {
  print "axiom AuditUntrusted : False"
  print "theorem EDSL.auditRejectionProbe : False := AuditUntrusted"
} { print }' scripts/Audit.lean > "$negative_source"

if lake env lean "$negative_source" > "$negative_log" 2>&1; then
    echo 'Axiom audit incorrectly accepted an untrusted transitive dependency'
    exit 1
fi
negative_message=$(cat "$negative_log")
if [[ "$negative_message" != *'depends on unapproved axiom AuditUntrusted'* ]]; then
    cat "$negative_log"
    echo 'Negative audit check failed for an unexpected reason'
    exit 1
fi
echo 'Axiom audit rejected the untrusted transitive dependency'
