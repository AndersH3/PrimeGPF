# Prime GPF magma: extended Lean proof scripts

**Latest repair:** the user reports successful builds of Core and Statements.
The next failure in Elementary.fixed_criterion is repaired by using
`Nat.succ_pos` for positivity of the quotient plus one. See
`ELEMENTARY_FIX.md`. This latest change awaits a new compiler run.

**Status: incomplete and NOT compiler-verified.** This revision adds substantial
proof scripts to the uploaded draft, but neither the old nor the new Lean code
has been compiled in this environment. Lean and Lake are absent, and the
attempted toolchain download was blocked/cancelled by the environment.
Tactic, elaboration, or other compilation errors may remain.

The source compendium has 39 numbered results. This package now supplies:

| Development status | Original draft | This revision |
|---|---:|---:|
| Full proof scripts, uncompiled | 22 | 31 |
| Conditional proof scripts, uncompiled | 9 | 5 |
| Partial proof scripts, uncompiled | 1 | 0 |
| Statements only | 6 | 2 |
| False original statement | 1 | 1 |

The **corrected 5.5** also has a new full script, outside the 39-result count.
“Full script” does not mean Lean has accepted it. No mathematical proposition
has been proved merely by defining it or assuming it as a theorem parameter.

## What was added

| File | New work |
|---|---|
| `PrimeGPF/DirectExponential.lean` | Elementary odd-cofactor argument; complete scripts for 8.1 and 3.5 without Zsigmondy |
| `PrimeGPF/Orders.lean` | Equivalence with mathlib orderOf; positive-order divisibility; dyadic forcing; 5.2, 5.3, 8.2 and corrected 5.5 |
| `PrimeGPF/Quadratic.lean` | Bridge to quadraticChar; 5.4; explicit discriminant witness; reciprocity at five; 9.6 and 9.8 |
| `PrimeGPF/Unbounded.lean` | All three clauses of 6.4 using mathlib's Dirichlet theorem |
| `PrimeGPF/Progressions.lean` | General affine residue lemma; arithmetic and exact count identities in 6.1; remaining PNT-AP limit isolated |
| `PrimeGPF/Conditional.lean` | Refutation and repair of the old order dependency; wrappers reducing 8.3, 8.4, 8.5 and 9.3 to ZsigmondyInput alone |

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

Original 5.5 is still false at p=3, q=5, m=1. Its refutation is retained;
`proof_5_5_corrected` targets the separately named statement with r ≠ 2.

## Remaining work

- **8.3, 8.4, 8.5, 9.3:** `ZsigmondyInput`, the specialized primitive-divisor existence theorem.
- **6.1:** `PrimeAPInput`, the specified prime-number-theorem ratio limit for arithmetic progressions.
- **6.2:** smooth-number box counting and uniform polylogarithmic estimates.
- **6.3:** relative-density and pair-density limits.
- **Every supplied script:** Lean compilation and any necessary repairs.

See `COVERAGE.md`, `MATHEMATICAL_NOTES.md` and `coverage.json` for details.

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
**2 after a successful draft build**, because mathematical obligations remain.
The intentional exit 2 is not a compilation failure. No successful build log
is included in this revision.

`Audit.lean` requests axioms for all 126 theorem declarations and displays the
types of the two remaining external-input wrappers. Standard foundational
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
