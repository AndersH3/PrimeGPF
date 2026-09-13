# Four unconditional exponential results

This patch proves `PrimeGPF.proof_zsigmondy_dependency : ZsigmondyInput` and
instantiates the existing implication theorems for **8.3, 8.4, 8.5 and 9.3**.

The module and all 11 theorem axiom checks passed under Lean 4.19.0 during this
conversation. Only `propext`, `Classical.choice`, and `Quot.sound` occurred.
The source was recovered verbatim from the recorded successful run after a
workspace refresh. See evidence/VERIFICATION.md for the precise scope and limitations.

On the corrected local inventory in your handoff, the resulting totals are
**37 unconditional / 2 conditional**. Only 6.1 and 6.3 remain conditional on
`PrimeAPInput`. The historical false version of 5.5 is not counted.

## Apply to the existing checkout

```bash
cd ~/Documents/prime_gpf_lean_new/prime_gpf_lean
unzip -o ~/Downloads/prime_gpf_zsigmondy_proof.zip -d .
bash verify_prime_exponent.sh
python3 integrate_prime_exponent.py
python3 tools/check_sources.py
lake build
lake env lean Audit.lean
./verify.sh
```

The extension verification exits 0 on success. The existing global `verify.sh`
may intentionally exit 2 while `PrimeAPInput` remains outstanding.
The integration helper requires a successful fresh verification record matching
the source hash. It appends the import and audit commands, updates only the four
coverage rows, and retains backups. Existing Counting, Density, FiveFive and
other mathematical source files are preserved.

No Lean or mathlib upgrade is required. The repository's committed manifest at
`4b0f848c99777fc5f0e088b4bb2b80dd458a09e4` resolves mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0), which was used for validation.

The computer-local checkout in the handoff is not mounted in this workspace.
Its unpublished Density.lean and corrected metadata therefore have not been
committed or pushed. This patch is an addition to that checkout, not a replacement.

See PROOF.md for the argument and pinned GitHub sources. PNT_RESEARCH.md records
the remaining research route; no experimental PNT proof is included or counted.
