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
python3 - <<'PY'
import json, re, sys
from pathlib import Path
coverage = json.loads(Path('coverage.json').read_text())
text = Path('evidence/axioms.log').read_text()
found = {n: {a.strip() for a in deps.split(',') if a.strip()}
         for n, deps in re.findall(r"'(.+?)' depends on axioms:\s*\[([^\]]*)\]", text)}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert found, 'No axiom audit output found.'
for n, deps in found.items():
    assert deps <= allowed, (n, deps - allowed)
remaining = [r for r in coverage['results'] if
             r['status'] != 'full_script_verified' or not r['compiler_verified']]
complete = len(coverage['results']) == 39 and not remaining
if complete:
    assert 'PrimeGPF.proof_all_39' in found, 'The conjunction of all 39 results was not audited.'
report = {'lean_build_succeeded': True, 'axiom_audit_passed': True,
          'complete_formalization': complete,
          'remaining_results': [r['id'] for r in remaining],
          'combined_theorem': 'PrimeGPF.proof_all_39' if complete else None}
Path('evidence/local_build_status.json').write_text(json.dumps(report, indent=2)+'\n')
if complete:
    print('PASS: all 39 corrected results compiled and passed the transitive axiom audit.')
else:
    print(f'Project compiled; {len(remaining)} results remain incomplete or conditional.')
sys.exit(0 if complete else 2)
PY
bash verify_extensions.sh
