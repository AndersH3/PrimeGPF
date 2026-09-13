#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p evidence
python3 tools/check_sources.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'Lean/Lake is unavailable. No formal verification was performed.' >&2
  exit 127
fi
lake env lean --version | tee evidence/lean-version.txt
lake build 2>&1 | tee evidence/build.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
if grep -Eq 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler' evidence/axioms.log; then
  echo 'The axiom audit contains an admission or compiler-trust dependency.' >&2
  exit 1
fi
python3 - <<'PY'
import json
from pathlib import Path
p=Path('coverage.json')
s=json.loads(p.read_text())
report={'draft_build_succeeded':True,'axiom_report_generated':True,
        'complete_formalization':False,
        'notice':'Statements and conditional proofs do not discharge missing proofs.'}
Path('evidence/local_build_status.json').write_text(json.dumps(report,indent=2)+'\n')
remaining=[r for r in s['results'] if r['status']!='full_script_uncompiled']
print(f'Draft compiled; {len(remaining)} entries still require correction or further proof development.')
print('Review evidence/axioms.log and COVERAGE.md. This is not a completed formalization.')
PY
exit 2
