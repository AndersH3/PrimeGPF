#!/usr/bin/env python3
"""Integrate only after verify_prime_exponent.sh succeeds; preserve local work."""
from pathlib import Path
import collections, hashlib, json
root = Path(__file__).resolve().parent
p = root / 'PrimeGPF/PrimeExponent.lean'
report_path = root / 'evidence/prime-exponent-status.json'
if not report_path.exists():
    raise SystemExit('Run bash verify_prime_exponent.sh successfully before integration.')
report = json.loads(report_path.read_text())
if not (report.get('module_compiled') and report.get('axiom_audit_passed') and
        report.get('module_sha256') == hashlib.sha256(p.read_bytes()).hexdigest()):
    raise SystemExit('The verification record does not match this module. Re-run verification.')
coverage_path = root / 'coverage.json'
coverage = json.loads(coverage_path.read_text())
rows = {r['id']: r for r in coverage['results']}
proofs = {'8.3': 'proof_8_3', '8.4': 'proof_8_4', '8.5': 'proof_8_5', '9.3': 'proof_9_3'}
for ident, proof in proofs.items():
    row = rows[ident]
    if row['statement'] != 't' + ident.replace('.', '_'):
        raise SystemExit(f'Unexpected statement for {ident}; no files changed.')
    row.update(status='full_script_verified', compiler_verified=True,
               proofs=[proof] + [n for n in row['proofs'] if n != proof],
               note='Unconditional: PrimeExponent.lean proves ZsigmondyInput using lifting the exponent and finite-field orders.')
coverage['counts'] = dict(collections.Counter(r['status'] for r in coverage['results']))
full = sum(r['compiler_verified'] and r['status'] in ('full_script_verified', 'full_script_uncompiled')
           for r in coverage['results'])
coverage['complete_formalization'] = full == len(coverage['results'])
main = root / 'PrimeGPF.lean'
s = main.read_text()
new_import = 'import PrimeGPF.PrimeExponent'
if new_import not in s.splitlines():
    s = s.rstrip() + '\n' + new_import + '\n'
audit = root / 'Audit.lean'
a = audit.read_text()
for name in report['audited_theorems']:
    line = '#print axioms ' + name
    if line not in a.splitlines():
        a = a.rstrip() + '\n' + line + '\n'
status = ('# Primitive-divisor milestone\n\n'
          'Results 8.3, 8.4, 8.5 and 9.3 are now unconditional.\n'
          '`PrimeGPF.proof_zsigmondy_dependency` proves the external input itself.\n\n'
          f'The current local inventory records **{full} full verified results out of 39**.\n'
          'Other rows, including corrected 5.5 and the local 6.3 work, were preserved.\n\n'
          'PrimeAPInput remains unproved. See PROOF.md for the argument and sources.\n')
updates = [(main, s), (audit, a),
           (coverage_path, json.dumps(coverage, indent=2, ensure_ascii=False) + '\n'),
           (root / 'PRIME_EXPONENT_STATUS.md', status)]
notice = ('> Primitive-divisor update: results 8.3, 8.4, 8.5 and 9.3 are now unconditional. '
          'See [the current milestone](PRIME_EXPONENT_STATUS.md) and `coverage.json`; '
          'older status text below predates this update.\n\n')
for name in ['COVERAGE.md', 'README.md']:
    path = root / name
    if path.exists() and not path.read_text().startswith(notice):
        updates.append((path, notice + path.read_text()))
for path, content in updates:
    if path.exists():
        backup = path.with_name(path.name + '.before-prime-exponent')
        if not backup.exists():
            backup.write_bytes(path.read_bytes())
    path.write_text(content)
print(f'Integrated four unconditional results; local full-verified count: {full}/39.')
print('Run python3 tools/check_sources.py, lake build, lake env lean Audit.lean, then ./verify.sh.')
print('An exit status of 2 from verify.sh is expected while PrimeAPInput remains outstanding.')
