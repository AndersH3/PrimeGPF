#!/usr/bin/env python3
"""Check completeness and allowed transitive axioms of the extension audit.

This script validates an actual Lean audit log; it is not a substitute for
compilation. Run verify_extensions.sh to generate the log and build evidence.
The historical 39-result coverage inventory is deliberately kept separate.
"""
from pathlib import Path
import json
import re
import subprocess

root = Path(__file__).resolve().parents[1]
expected = set()
for path in sorted((root / 'PrimeGPF' / 'Extensions').glob('*.lean')):
    expected.update('PrimeGPF.Extensions.' + name for name in
                    re.findall(r'^(?:@\[[^\]]*\]\s*)?theorem\s+(\w+)', path.read_text(), re.M))
log = (root / 'evidence' / 'extensions-axioms.log').read_text()
found = {name: {a.strip() for a in axioms.split(',') if a.strip()}
         for name, axioms in re.findall(
             r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    found[name] = set()
assert expected, 'No extension declarations found.'
assert set(found) == expected, {
    'missing': sorted(expected - set(found)),
    'unexpected': sorted(set(found) - expected),
}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in found.items():
    assert axioms <= allowed, (name, sorted(axioms - allowed))
report = {
    'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root,
                                      text=True).strip(),
    'extension_axiom_audit_passed': True,
    'audited_declaration_count': len(found),
    'axioms': {name: sorted(found[name]) for name in sorted(found)},
    'scope': 'Extensions 5, 6, 8, 9 and algebraic 10; original inventory remains 39.',
}
(root / 'evidence' / 'extensions-status.json').write_text(
    json.dumps(report, indent=2) + '\n')
print(f'PASS: {len(found)} extension declarations passed the transitive axiom audit.')
