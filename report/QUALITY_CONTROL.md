# Quality-control record

Revision: 14 September 2026.

## Source and proof status

- Edited `prime_gpf_report.tex`, `diagrams.tex`, and `prime_gpf_sources.bib`; the PDF was regenerated from LaTeX, with no direct PDF content edits.
- Compared the report with main proof snapshot `9c60cd35f329dc7380d3a17db6da23cbe7c54e9d` and checked all 39 status-table rows against existing numbered theorem declarations.
- Completion evidence is the successful [full Lean build and transitive axiom audit](https://github.com/AndersH3/PrimeGPF/actions/runs/34798956017) for `f169752012e60d0decda7533c3edbc427c759d59`, subsequently merged into that snapshot. GitHub reports completion on 14 September 2026. `proof_all_39` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- This report-only revision changes no Lean proof or statement and does not claim a fresh Lean or Agda run. The repository is private; source and CI links require access.

## Document build and inspection

- `bash build.sh` completed successfully: XeLaTeX → biber → XeLaTeX → XeLaTeX.
- Build environment: XeTeX/TeX Live 2023, biblatex 3.22 and biber 2.22; Latin Modern Roman, Sans and Math, plus DejaVu Sans Mono. The source supplies compatibility conditionals for older LaTeX kernels without optional PDF metadata management.
- Final PDF: 33 A4 pages. No undefined citations or cross-references, missing-character warnings, or outstanding rerun requests in the final LaTeX log.
- Checked all pages using rendered contact sheets and detailed views of the dependency diagram, Chapters 6 and 8, status/declaration tables, and bibliography. No visible clipping or broken operation symbols were found.
- Corrected empty alphabetic labels on newly added online references by assigning explicit citation shorthands. Added explicit Unicode mappings and preserved spacing in Lean listings.
- Extracted-text checks confirm the three operation symbols, all-39 completion statement, new proof declarations, and AI disclosure; no Unicode replacement characters occur.
- Three residual tabularray `Overfull \hbox` messages of 10.95 pt remain at table construction boundaries. They contain no overflowing text in the log; the rendered status and declaration tables fit within the page and were visually checked. Ordinary prose and bibliography have no overfull-box warnings.
- The source archive contains the LaTeX, bibliography, diagram, build script, revision/review/build records, and regenerated PDF. Build caches and temporary logs are excluded.

The review response is recorded in `PEER_REVIEW_RESPONSE.md`. Visual inspection and compilation do not replace human review of the informal/formal statement correspondence or bibliographic accuracy.
