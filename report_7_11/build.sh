#!/bin/bash
# Cleanup
rm *.aux *.bbl *.blg *.log *.out *.synctex.gz
# First run
bibtex review_7
pdflatex -synctex=1 review_7.tex
echo '---'
bibtex review_11
pdflatex -synctex=1 review_11.tex
# Second time for bib
echo '---'
bibtex review_7
pdflatex -synctex=1 review_7.tex
echo '---'
bibtex review_11
pdflatex -synctex=1 review_11.tex
# Third time for bib
echo '---'
bibtex review_7
pdflatex -synctex=1 review_7.tex
echo '---'
bibtex review_11
pdflatex -synctex=1 review_11.tex