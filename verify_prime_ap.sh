#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p evidence
lake env lean --version | tee evidence/prime-ap-version.log
lake build PrimeGPF.PrimeAP 2>&1 | tee evidence/prime-ap-build.log
lake env lean PrimeAPAudit.lean 2>&1 | tee evidence/prime-ap-axioms.log
python3 - <<'PY'
from pathlib import Path
import hashlib, json, re
expected = {"WienerIkeharaTheorem'", 'PrimeGPF.Analytic.mangoldt_AP_limit',
    'PrimeGPF.Analytic.theta_AP_limit', 'PrimeGPF.Analytic.counting_limit_of_weighted',
    'PrimeGPF.apCount_log_limit', 'PrimeGPF.proof_primeAP_dependency',
    'PrimeGPF.proof_6_1', 'PrimeGPF.proof_6_3'}
text = Path('evidence/prime-ap-axioms.log').read_text()
found = {n: {a.strip() for a in deps.split(',') if a.strip()}
         for n, deps in re.findall(r"'(.+?)' depends on axioms:\s*\[([^\]]*)\]", text)}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert expected <= found.keys(), expected - found.keys()
for n in expected:
    assert found[n] <= allowed, (n, found[n] - allowed)
paths = sorted(Path('PrimeGPF/PNT').rglob('*.lean')) + [
    Path('PrimeGPF') / n for n in ['PrimeAPAnalytic.lean', 'WeightedCounting.lean', 'PrimeAP.lean']]
hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
for p in paths:
    assert not re.search(r'\b(sorry|admit|proof_wanted|native_decide|unsafe)\b', p.read_text()), p
Path('evidence/prime-ap-status.json').write_text(json.dumps({
    'compiled': True, 'axiom_audit_passed': True,
    'audited': sorted(expected), 'sha256': hashes}, indent=2) + '\n')
print('PASS: PrimeAPInput, 6.1 and 6.3 compiled and passed the transitive axiom audit.')
PY
