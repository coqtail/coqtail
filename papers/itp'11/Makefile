all: dequa

dequa:
	pdflatex dequa.tex
	bibtex dequa.aux
	pdflatex dequa.tex
todos:
	grep "TODO" *.tex > TODO
	cat TODO

clean:
	rm -f *.aux *.log *.bak *.pdf
