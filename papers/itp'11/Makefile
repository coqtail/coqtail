all: dequa todos

dequa:
	pdflatex dequa.tex

todos:
	grep "TODO" *.tex > TODO
	cat TODO

clean:
	rm -f *.aux *.log *.pdf
