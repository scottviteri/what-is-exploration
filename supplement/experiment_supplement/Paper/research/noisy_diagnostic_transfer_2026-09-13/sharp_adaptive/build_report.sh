#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
pandoc REPORT.md --standalone --from=markdown+tex_math_dollars --to=latex --output=report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex > report.build.log
pdflatex -interaction=nonstopmode -halt-on-error report.tex >> report.build.log
