# Prime GPF magma: Lean formalization

All **39 corrected numbered results** now have unconditional proofs in
**Lean 4.19.0**, using pinned mathlib v4.19.0
(`c44e0c8ee63ca166450922a373c7409c5d26b00b`).

Results **6.1 and 6.3**, including their shared `PrimeAPInput`, passed the
[Lean build and transitive axiom audit](https://github.com/AndersH3/PrimeGPF/actions/runs/34795580169).
`PrimeGPF.proof_all_39` combines all 39 corrected numbered statements.
The audit allows only `propext`, `Classical.choice`, and `Quot.sound`.

| Status | Count |
|---|---:|
| Unconditional compiler-verified numbered results | 39 |
| Conditional numbered results | 0 |

## New prime-AP proof

The proof applies a proved Wiener–Ikehara theorem to von Mangoldt restricted
to a reduced residue class, supplying its summability and Chebyshev hypotheses.
It removes higher prime powers and converts the logarithmically weighted sum
to ordinary prime counts. It then proves the exact `Claims.APAsymptotic`
normalization and `PrimeAPInput`. The existing density reductions give 6.3.

| Module | Contents |
|---|---|
| `PrimeGPF/PrimeAPAnalytic.lean` | Residue-class weighted asymptotics and removal of higher prime powers |
| `PrimeGPF/WeightedCounting.lean` | Conversion from weighted sums to counts |
| `PrimeGPF/PrimeAP.lean` | `proof_primeAP_dependency`, `proof_6_1`, `proof_6_3` |
| `PrimeGPF/Complete.lean` | Conjunction of all 39 corrected numbered propositions |

The analytic dependencies are adapted from a version-compatible
[PrimeNumberTheoremAnd revision](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/d3cea76119684a766d2cd195b05b137442205653).
[PNT_PROVENANCE.md](PNT_PROVENANCE.md) records the source, excluded unfinished
sections, and compatibility edit. The Apache 2.0 license and copyright notices
are retained.

The earlier root-level proof experiments and both development histories are
preserved. Their abstract Wiener–Ikehara interface remains a conditional
research interface; the final proofs use the proved analytic dependency.

## Build and audit

With Elan installed, from the repository directory:

```bash
lake exe cache get
bash verify.sh
```

For the prime-AP input and results 6.1 and 6.3 alone:

```bash
bash verify_prime_ap.sh
```

The full verifier builds the project, compiles `Audit.lean`, enforces the
axiom allowlist, and requires the `proof_all_39` audit before reporting
completeness. It returns **0** on success, **127** if Lake is unavailable,
and a nonzero status on compilation or audit failure. Logs are written
under `evidence/`. Static inventory checks do not replace compilation.

[GitHub Actions](https://github.com/AndersH3/PrimeGPF/actions/workflows/primeap-experiment.yml)
runs the checks and publishes the logs. See [COVERAGE.md](COVERAGE.md) and
`coverage.json` for the current inventory. Earlier status and evidence files
describe historical development stages.

## Previously corrected statements

Official theorem 5.5 includes the necessary `r ≠ 2` hypothesis. The
originally printed statement is false at `p=3, q=5, m=1`; it and its
verified refutation remain separately available.

The corrected `OrderDividesPrimePred` requires a positive exponent. Its old
version is separately refuted at `(r,p,k)=(3,2,0)`. These corrections predate
the prime-AP work. This update changes no numbered proposition definitions.
The original Word source remains unchanged.

The supplied mathematical theory is attributed to Anders Hellström. The Lean
development includes AI assistance and credited upstream formalizations.
