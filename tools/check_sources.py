#!/usr/bin/env python3
"""Static inventory checks only. Does not parse or type-check Lean."""
from pathlib import Path
import json, re
root = Path(__file__).resolve().parents[1]

def uncomment(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-': depth += 1; i += 2
        elif depth and text[i:i+2] == '-/': depth -= 1; i += 2
        elif depth: i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        else: result.append(text[i]); i += 1
    if depth: raise AssertionError('Unclosed block comment')
    return ''.join(result)

files = sorted((root/'PrimeGPF').rglob('*.lean'))
source = '\n'.join(uncomment(p.read_text()) for p in files)
for token in ('sorry', 'admit', 'axiom', 'unsafe', 'native_decide'):
    assert not re.search(r'\b'+token+r'\b', source), f'Forbidden proof shortcut: {token}'
coverage = json.loads((root/'coverage.json').read_text())
assert len(coverage['results']) == 39
expected = {f'{chapter}.{i}' for chapter,count in [(3,8),(4,3),(5,6),(6,4),(7,5),(8,5),(9,8)] for i in range(1,count+1)}
assert {r['id'] for r in coverage['results']} == expected
for row in coverage['results']:
    assert re.search(r'\bdef\s+'+re.escape(row['statement'])+r'\b', source), row
    for proof in row['proofs']:
        assert re.search(r'\btheorem\s+'+re.escape(proof)+r'\b', source), row
print('Static checks passed: 39 inventory entries, declarations present, no proof shortcuts.')
print('This check is not Lean compilation or proof validation.')
