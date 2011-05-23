all: main.pdf

%.pdf : %.tex
	pdflatex $<

clean:
	rm -f *.aux *.log *.pdf
