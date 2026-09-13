# Prime GPF magma: Lean formalization

**Status:** the project builds successfully under **Lean 4.19.0** with
mathlib **v4.19.0**. The axiom audit contains no `sorryAx`, `admit`,
`native_decide`, or compiler-trust shortcuts.

The source compendium contains 39 numbered results. Current status:

| Status | Count |
|---|---:|
| Complete compiler-verified proofs | 33 |
| Compiler-verified conditional proofs | 6 |
| Statement only | 0 |
| False numbered statements | 0 |

The official numbered theorem 5.5 is the corrected version with the necessary
`r ≠ 2` hypothesis. The old printed version is retained separately only for
its verified counterexample and refutation.

Result **6.2 (polylogarithmic fibers)** is now completely and unconditionally
proved. The proof includes an exponent-vector bound for smooth numbers,
a polylogarithmic smooth-number estimate, injections from additive and
multiplicative fibers into bounded smooth cofactors, and the required common
constant depending only on `r`.

Result **6.3 (zero density)** now has a compiler-verified conditional proof.
Both fixed-anchor relative-density limits and the two-variable pair-density
limits are derived from `PrimeAPInput`, the same PNT-in-arithmetic-progressions
input already isolated for 6.1. No additional external analytic hypothesis is
introduced.

## What was added

| File | New work |
|---|---|
| `PrimeGPF/DirectExponential.lean` | Elementary odd-cofactor argument; complete scripts for 8.1 and 3.5 without Zsigmondy |
| `PrimeGPF/Orders.lean` | Equivalence with mathlib orderOf; positive-order divisibility; dyadic forcing; 5.2, 5.3, 8.2 and corrected 5.5 |
| `PrimeGPF/Quadratic.lean` | Bridge to quadraticChar; 5.4; explicit discriminant witness; reciprocity at five; 9.6 and 9.8 |
| `PrimeGPF/Unbounded.lean` | All three clauses of 6.4 using mathlib's Dirichlet theorem |
| `PrimeGPF/Progressions.lean` | General affine residue lemma; arithmetic and exact count identities in 6.1; remaining PNT-AP limit isolated |
| `PrimeGPF/Conditional.lean` | Refutation and repair of the old order dependency; wrappers reducing 8.3, 8.4, 8.5 and 9.3 to ZsigmondyInput alone |
| `PrimeGPF/Counting.lean` | Complete proof of 6.2 plus finite additive and multiplicative pair-count bounds via injections into bounded smooth cofactors |
| `PrimeGPF/Density.lean` | Conditional proof of 6.3 from `PrimeAPInput`: AP and prime-count asymptotics, relative-zero estimates, and additive/multiplicative pair-density zero |

The original operations and the 39 source proposition definitions are retained.
The original Word source is included unchanged.

## A newly discovered false dependency

The old definition `OrderDividesPrimePred` claimed that every
`PrimitiveDivisor r p k` implies `k ∣ r - 1`. However, the draft's
`PrimitiveDivisor` definition allows **k = 0**. Thus
`PrimitiveDivisor 3 2 0` holds, while `0 ∣ 2` is false.

This revision preserves that proposition as `OrderDividesPrimePredOriginal`
and supplies `refutation_order_dependency`. The corrected
`OrderDividesPrimePred` explicitly requires `0 < k`; its script is
`proof_order_dependency`. The caller for exponent `2*q` now supplies positivity.
No source claim was silently weakened to close this gap.

The originally printed 5.5 is false at p=3, q=5, m=1. Its refutation is
retained as historical evidence. The official numbered 5.5 now includes
`r ≠ 2` and is proved by `proof_5_5`.

## Remaining work

- **6.1 and 6.3:** `PrimeAPInput`, the specified PNT-in-arithmetic-progressions ratio limit. The entire density argument for 6.3 is now proved from this same input.
- **8.3, 8.4, 8.5, 9.3:** `ZsigmondyInput`, the specialized primitive-divisor existence theorem.

All currently supplied Lean proof scripts and conditional wrappers compile.

## Build locally

The target remains Lean **4.19.0** and mathlib **v4.19.0**.
With Lean/Elan installed and Internet access available, run:

```bash
cd prime_gpf_lean
bash bootstrap_and_verify.sh
```

Equivalently:

```bash
lake update
lake exe cache get
bash verify.sh
```

The verification script preserves build and axiom logs. It fails on a compiler
error or forbidden axiom dependency. It returns **127** if Lake is absent and
**2 after a successful build** while mathematical obligations remain. The
intentional exit 2 is not a compilation failure.

`Audit.lean` requests axioms for the project theorem declarations and displays
the types of the remaining external-input wrappers. Standard foundational
axioms (choice, propositional extensionality, quotient soundness) are allowed;
proof admissions and compiler-trust shortcuts are not.

To diagnose a failed module after its imports have built:

```bash
lake env lean PrimeGPF/Orders.lean
```

Static checks and arithmetic spot-checks are supporting development evidence,
not Lean verification. `evidence/revision_verification_attempt.log` records the
actual failed build attempt; `evidence/revision_status.json` records its status.
The old authoring notes in `evidence/original_*` are historical only.

This package was generated with AI assistance. Mathematical authorship of the
supplied theory is attributed to Anders Hellström; the Lean translations,
new proof arguments, repairs and audit notes require review and compilation.
