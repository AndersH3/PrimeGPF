#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
rm -f prime_gpf_report.{aux,bbl,bcf,blg,log,out,run.xml,toc,lof,lot}
xelatex -interaction=nonstopmode -halt-on-error prime_gpf_report.tex
biber prime_gpf_report
xelatex -interaction=nonstopmode -halt-on-error prime_gpf_report.tex
xelatex -interaction=nonstopmode -halt-on-error prime_gpf_report.tex
