# Change log — revised Prime-GPF theorem compendium

Date: 2026-09-13

## Mathematical corrections
- Made the corrected theorem 5.5 (with the necessary `r ≠ 2` hypothesis) the official numbered statement in the report; retained the old `r = 2` counterexample as historical evidence.
- Updated theorem 6.2 to unconditional, compiler-verified status and described the explicit smooth exponent-box/cardinality proof.
- Updated theorem 6.3 to a compiler-verified implication from `PrimeAPInput`, including the fixed-anchor and pair-density proof architecture.
- Marked precisely the six remaining conditional numbered results: 6.1, 6.3, 8.3, 8.4, 8.5, and 9.3.

## Lean-proof integration
- Added a 39-result status table with principal declarations/modules.
- Explained the distinction between a proposition definition, a checked conditional theorem, and a proof of its external input.
- Added discussion of the project's audit policy and accepted foundational axioms.
- Added a source-module guide and dependency diagram.

## Explanatory additions
- Added self-contained explanations of greatest prime factors, magmas, fibers, smooth numbers, `ZMod`, multiplicative order, primitive divisors, cyclotomic polynomials, quadratic characters, PNT in arithmetic progressions, filters/Tendsto, density, and finite dynamics.
- Expanded informal proof strategies throughout.

## Literature / novelty search
- Added classical sources for smooth numbers, PNT-AP, cyclotomic theory, quadratic reciprocity, and Bang-Zsigmondy.
- Added current formalization context from mathlib's `PrimesInAP` module and the public `PrimeNumberTheoremAnd` project, carefully distinguishing these from the pinned PrimeGPF dependency.
- Identified prior work by Caragiu, Back, Scheckelhoff, and Vicol on greatest-prime-factor prime magmas and recurrences.
- Added a dated novelty-search methodology and cautious conclusions; no absolute originality claim is made.

## Typesetting / document design
- Rebuilt as a single XeLaTeX/KOMA-Script `scrbook` document with thematic chapters.
- Added narrow margins, TOC, semantic cross-references, tcolorbox callouts, tabularray tables, TikZ diagrams, code listings, bookmarks, hyperlinks, and a biber/biblatex bibliography.
- Added a prominent front-matter AI disclosure and a complete disclosure appendix.

## Reproducibility
Run `./build.sh` in the project folder. The build uses XeLaTeX and biber.

- Corrected a prompt-induced terminology bug: removed “Lecture N” from chapter titles and replaced the one prose reference with “chapter”; the document is now consistently organized as a book/report by chapters.
