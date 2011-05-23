all: main.pdf

%.pdf : %.tex ref.bib Makefile
	pdflatex $(<:.tex=)
	bibtex $(<:.tex=)
	pdflatex $(<:.tex=)

clean:
	rm -f *.aux *.log *.pdf
