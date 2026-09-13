# Building the report

Requirements: XeLaTeX, biber, and the LaTeX packages referenced in `prime_gpf_report.tex`.

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
