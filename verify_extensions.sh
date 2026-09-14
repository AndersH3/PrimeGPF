#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p evidence
python3 tools/check_sources.py
lake build PrimeGPF.Extensions 2>&1 | tee evidence/extensions-build.log
lake env lean ExtensionAudit.lean 2>&1 | tee evidence/extensions-axioms.log
python3 tools/check_extension_audit.py
