# Response to the peer review

Revision: 14 September 2026. Source: `prime_gpf_report.tex`, with `diagrams.tex` and `prime_gpf_sources.bib`. The PDF is generated from these files.

The review describes the earlier 33-unconditional/6-conditional manuscript. The revised report follows the completed proof repository at main commit `9c60cd35f329dc7380d3a17db6da23cbe7c54e9d`.

| Review point | Revision |
| --- | --- |
| Unresolved `PrimeAPInput`, particularly 6.1 and 6.3 | Chapter 6 explains the completed proof using a proved Wiener–Ikehara theorem, pinned mathlib analytic continuation, removal of proper prime powers, and a proved weighted-count conversion. Source provenance and the excluded unfinished upstream formulations are explicit. |
| Reliance on `ZsigmondyInput` in Section 8 | Chapter 8 explains the completed specialized prime-exponent proof via an odd cofactor, lifting the exponent, and exact multiplicative order. Results 8.3–8.5 and 9.3 are unconditional. The report does not claim a formalization of the full general Bang–Zsigmondy theorem. |
| Feasibility and roadmap for the dependencies | The former roadmap is replaced by the implemented construction. Future work concerns upstream integration, API maintenance, and optional generalizations; none is needed to close the 39-result inventory. No unsupported effort estimate is assigned to a full general Zsigmondy development. |
| Formal engineering versus mathematical novelty | The contribution remains framed as synthesis, correction, and mechanization. Classical analytic and valuation ingredients are credited, and the Caragiu–Back prior art is retained. |
| Fractured notation | The LaTeX consistently uses `\boxplus`, `\boxtimes`, and the `\gexp` macro for the GPF operations. Mathematical notation is checked in the rendered output as well as in extracted text. |
| Custom `gpf` interoperability | Chapter 2 explains specification-based interoperability through `gpf_eq_of_spec`, including the totalized values at 0 and 1. It does not claim an already implemented bridge to every external GPF API or an efficient factorization implementation. |
| Theorem 5.5 correction | The necessary odd-prime restriction and the historical counterexample are preserved; the formal theorem proves the corrected statement. |
| Trust boundaries and AI transparency | The abstract, Chapter 1, module/status chapter, and AI appendix now distinguish checked proof terms, retained conditional interfaces with proved premises, historical metadata, and report authorship. `proof_all_39` and its transitive axiom audit provide the completion evidence. |

Validation evidence: [successful full Lean build and axiom audit](https://github.com/AndersH3/PrimeGPF/actions/runs/34798956017), for proof commit `f169752012e60d0decda7533c3edbc427c759d59`, subsequently merged into the main snapshot above. The accepted foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The Agda companion is described as computational work, not a duplicate verification of all 39 theorems.

The repository is private at this revision; the source and CI links require access. A public archival release remains a reproducibility improvement.

See `QUALITY_CONTROL.md` for the separate LaTeX build and visual checks. No Lean theorem statement or proof was changed in this report-only revision.
