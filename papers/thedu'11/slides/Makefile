#; we run pdflatex 2 times in order to get the
# page index right

all: slides

slides:
	pdflatex main
	pdflatex main

clean:
	rm -rf *.log *.aux *.toc *.snm *.out *.pdf *.nav
