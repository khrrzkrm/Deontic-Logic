NAME = exercise

.PHONY: clean pdfs

pdfs:
	latexmk -pdf $(NAME)
	latexmk -pdf $(NAME) -jobname=$(NAME)-solution

clean:
	latexmk -pdf -c $(NAME) -jobname=$(NAME)-solution
	latexmk -pdf -c $(NAME)
	rm -f comment.cut
