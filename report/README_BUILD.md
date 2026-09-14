# Building the report

Requirements: XeLaTeX, biber with a compatible biblatex release, and the LaTeX packages referenced in `prime_gpf_report.tex`. The fonts are Latin Modern Roman, Latin Modern Sans, Latin Modern Math, and DejaVu Sans Mono.

Edit `prime_gpf_report.tex`, `diagrams.tex`, or `prime_gpf_sources.bib`; regenerate the PDF from these sources. Do not edit the PDF directly. From this directory:

```bash
./build.sh
```

The script runs XeLaTeX, biber, then two additional XeLaTeX passes so that the table of contents, citations, bookmarks, and cross-references settle.

Primary files:
- `prime_gpf_report.tex` — main source
- `prime_gpf_sources.bib` — bibliography database
- `diagrams.tex` — TikZ figure source
- `build.sh` — reproducible build script
- `CHANGELOG.md` — revision summary
- `QUALITY_CONTROL.md` — final compilation/rendering checks

The proof snapshot and CI evidence are recorded in the manuscript and `QUALITY_CONTROL.md`. `PEER_REVIEW_RESPONSE.md` maps the review to the source revisions. Report compilation is separate from Lean proof verification.
