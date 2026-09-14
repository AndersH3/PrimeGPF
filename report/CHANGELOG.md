# Change log — revised Prime-GPF theorem compendium

## 2026-09-14 — completed proof inventory and peer-review revision

- Updated the LaTeX source, TikZ dependency diagram, and bibliography against main at `9c60cd35f329dc7380d3a17db6da23cbe7c54e9d`.
- Recorded all 39 corrected numbered results as unconditional, with the transitive axiom audit of `proof_all_39` and successful CI evidence.
- Explained the actual PNT-AP construction: proved Wiener–Ikehara input, residue-class von Mangoldt sums, prime-power removal, and weighted-to-ordinary counting.
- Explained the direct prime-exponent proof of `ZsigmondyInput` using the odd cofactor, lifting the exponent, and multiplicative order. Distinguished it from the full general Bang–Zsigmondy theorem.
- Updated declarations, module guide, status table, verification commands, repository provenance and access status, and future-work discussion.
- Addressed novelty, custom-gpf interoperability, notation, and the historical theorem-5.5 correction; added `PEER_REVIEW_RESPONSE.md`.
- Described the Agda computational companion without presenting it as a second proof of the full inventory.
- Switched to readily available Latin Modern text/math fonts, retaining DejaVu Sans Mono for Lean listings.
- Regenerated the PDF from LaTeX; no direct PDF content edits.

## 2026-09-13 — historical revision

The entries below describe the earlier 33-unconditional/6-conditional milestone and are superseded by the completion above.

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
