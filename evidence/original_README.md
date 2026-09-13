# Prime GPF magma formalization draft

This is an **incomplete, uncompiled Lean 4 formalization draft** of Anders
Hellström's *Theorem Compendium for Prime GPF Magmas*, dated 17 June 2026,
from `prime_gpf_magma_theorem_compendium_v2_word.docx`.

It is not a completed machine-checked proof of the theory. All 39 numbered
results have Lean proposition definitions. Of those, 22 have full proof
scripts written, nine have conditional proof scripts, one has a partial
proof, six have statements only, and one original statement is false.
“Full proof script” means a script has been supplied for the complete named
proposition with no proof holes. It does **not** mean Lean has accepted it.
Syntax, elaboration, tactic, and library compatibility errors may remain.

## The mathematical obstruction

Theorem 5.5 is false as printed. Take p=3, q=5, m=1. Then

- r = P⁺(3·5+1) = P⁺(16) = 2;
- q ≡ p^(2^m−1) (mod r), because both sides are 1 modulo 2;
- the claimed conclusion r ≡ 1 (mod 2^(m+1)) says 2 ≡ 1 (mod 4), which is false;
- the claimed order is 4, whereas 3 has order 1 modulo 2.

The proof incorrectly uses −1 ≠ 1 without excluding characteristic two.
`Claims.t5_5_original` retains the original statement, and
`refutation_5_5` is its refutation script. `Claims.t5_5_corrected` separately
adds **r ≠ 2**. A proof of this corrected statement remains outstanding.
No consistent formalization can prove the false original statement.

## Files and notation

| File | Contents |
|---|---|
| `PrimeGPF/Core.lean` | Executable GPF scan; its maximum specification; prime subtype; three operations; smoothness; fiber and prime-power lemmas; orbit definitions |
| `PrimeGPF/Statements.lean` | All 39 numbered propositions; corrected 5.5; precise counting and asymptotic definitions |
| `PrimeGPF/Elementary.lean` | Basic laws, explicit failures, fibers, fixed points, bridge identities, refutation of 5.5 |
| `PrimeGPF/Arithmetic.lean` | Inverse witnesses, parity, collision elimination, second-column rigidity, finite common outputs |
| `PrimeGPF/SmallFibers.lean` | All parts of 4.3 |
| `PrimeGPF/Dynamics.lean` | Finite-state eventual periodicity; general orbit lemmas; conditional 5.3 |
| `PrimeGPF/Conditional.lean` | Exponential consequences with explicit missing dependencies; conditional 9.8 |
| `COVERAGE.md` and `coverage.json` | Per-result status, proof names, and unresolved work |
| `MATHEMATICAL_NOTES.md` | Source corrections, proof gaps, conventions, and remaining development |
| `Audit.lean` | Requests the axioms used by every supplied theorem and helper |
| `Examples.lean` | Small tables, fibers, and anchored orbits |
| `tools/check_witnesses.py` | Independent arithmetic checks of 19 finite examples; not formal verification |
| `verify.sh` | Local build and axiom-audit command |
| `source/` | The original attachment and its SHA-256 hash |

`add p q`, `mul p q`, and `exp p q` mean respectively
P⁺(p+q+1), P⁺(pq+1), and P⁺(p^q+1). They do not mean ordinary arithmetic.
`operate o` works on the subtype of primes and returns a prime.
The lower-case arithmetic functions are total on natural numbers, but
substantive theorems explicitly require the relevant primality hypotheses.

`gpf n` is a transparent descending finite search. It is practical for the
small proof witnesses, not for large numerical experiments. The source's
PARI/GP factorization approach remains preferable for large calculations.
There is no claim that the appendix computations prove universal results.

## Local verification

The proposed target is Lean **4.19.0**, with mathlib's **v4.19.0** tag.
These versions are specified in `lean-toolchain` and `lakefile.toml`.
No compiler or mathlib installation was available in the authoring session;
the attempted toolchain download was blocked by network approval.
Consequently there is no successful build log in this package.

Install Lean using the [official installation instructions](https://lean-lang.org/install/).
After extracting the archive, run this in the `prime_gpf_lean` directory:

```bash
lake update
lake exe cache get
bash verify.sh
```

`lake update` resolves the pinned mathlib release and creates the Lake
manifest. `lake exe cache get` downloads precompiled mathlib dependencies.
The script then builds the supplied project and requests an axiom report.
It preserves logs and returns nonzero on compiler errors. Even if compilation
succeeds, it returns status **2** while the coverage inventory contains
missing or conditional proofs. That status deliberately distinguishes a
successful draft build from a complete formalization.

To inspect the first compilation problem directly:

```bash
lake env lean PrimeGPF/Core.lean
```

After a successful build, the small computational examples can be run with:

```bash
lake env lean Examples.lean
```

Do not replace failed proofs with proof holes merely to obtain a green build.
A successful compilation of a proposition *definition* is not a proof of it.
The conditional theorems retain their hypotheses even after compilation.

## Verification status and trust

No `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` is used as a Lean
source declaration/tactic in the project. Missing results are named
propositions, never global assumptions. Conditional results take explicit
proof arguments and are labelled as such. Standard Lean/mathlib foundational
axioms, such as propositional extensionality, choice, and quotient soundness,
may appear in the generated axiom report.

The authoring checks covered file integrity, correspondence with the 15 page
images in the attachment, proof-hole scanning, declaration coverage, and 19
finite arithmetic checks. They did **not** validate the Lean proof terms.

This package was generated with AI assistance. Mathematical authorship of
the supplied theory is attributed to Anders Hellström; the Lean translation,
audit notes, and proposed correction are AI-generated work requiring review.
The original Word file is included unchanged.
