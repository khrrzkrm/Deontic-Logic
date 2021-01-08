all: script presentation

script:
	latexmk -pdf script

presentation:
	latexmk -pdf presentation

force-all: force-script force-presentation

force-script:
	latexmk -pdf -g -f script

force-presentation:
	latexmk -pdf -g -f presentation

rm-extra-files:
	rm -f \
		*.presentation.nav \
		*.presentation.snm \
		*.presentation.vrb \
		*.script.bbl \
		*.script.maf \
		*.script.mtc*

clean: rm-extra-files
	latexmk -pdf -c presentation
	latexmk -pdf -c script

clear: rm-extra-files
	latexmk -pdf -C presentation
	latexmk -pdf -C script


.PHONY: clean

.PHONY: clear

.PHONY: rm-extra-files
