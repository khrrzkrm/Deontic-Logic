#!/bin/bash
pdflatex -synctex=1 -halt-on-error presentation.tex
echo "---"
pdflatex -synctex=1 -halt-on-error presentation.tex
echo "---"
