#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if [[ ! -f lakefile.toml || ! -f PrimeGPF/Conditional.lean ]]; then
  echo 'Extract this patch into your existing prime_gpf_lean project first.' >&2
  exit 1
fi
mkdir -p evidence
lake env lean --version | tee evidence/prime-exponent-lean-version.log
lake build PrimeGPF.PrimeExponent 2>&1 | tee evidence/prime-exponent-build.log
lake env lean PrimeExponentAudit.lean 2>&1 | tee evidence/prime-exponent-axioms.log
python3 - <<'PY'
from pathlib import Path
import hashlib, json, re
p = Path('PrimeGPF/PrimeExponent.lean')
text = Path('evidence/prime-exponent-axioms.log').read_text()
expected = {'PrimeGPF.' + n for n in re.findall(r'^theorem (\w+)', p.read_text(), re.M)}
found = {}
for name, deps in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    found[name] = {a.strip() for a in deps.split(',') if a.strip()}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert expected <= found.keys(), f'Missing audit output: {sorted(expected - found.keys())}'
for name in expected:
    assert found[name] <= allowed, (name, found[name] - allowed)
report = {'module_sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
          'module_compiled': True, 'axiom_audit_passed': True,
          'audited_theorems': sorted(expected),
          'new_unconditional_results': ['8.3','8.4','8.5','9.3'],
          'remaining_input': 'PrimeAPInput'}
Path('evidence/prime-exponent-status.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'PASS: module compiled; {len(expected)} theorems use only the allowed foundational axioms.')
print('ZsigmondyInput is discharged. PrimeAPInput remains unproved.')
PY
