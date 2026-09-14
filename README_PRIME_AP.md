# Completed prime-AP input

`PrimeGPF.proof_primeAP_dependency : PrimeAPInput` discharges the shared
dependency of 6.1 and 6.3. Both theorem wrappers have no external
mathematical hypotheses. They compiled under Lean 4.19.0 and passed the
transitive axiom audit in [run 34795580169](https://github.com/AndersH3/PrimeGPF/actions/runs/34795580169).

Run `bash verify_prime_ap.sh` for the targeted build and audit, or
`bash verify.sh` for the full 39-result conjunction.
See [README.md](README.md) and [PNT_PROVENANCE.md](PNT_PROVENANCE.md).
