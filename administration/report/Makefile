REPORT_NAME="report_coqtail"
ARTICLE_NAME="main"
PAPERS="../../papers"

all: report

report:
	pdflatex $(ARTICLE_NAME).tex
#	bibtex $(ARTICLE_NAME).aux
#	pdflatex $(ARTICLE_NAME).tex $(REPORT_NAME).pdf

build: report
	gs -dNOPAUSE -sDEVICE=pdfwrite -sOUTPUTFILE=$(REPORT_NAME).pdf -dBATCH $(ARTICLE_NAME).pdf $(PAPERS)/thedu\'11/main.pdf $(PAPERS)/coqworkshop/main.pdf $(PAPERS)/itp\'11/dequa.pdf


clean:
	rm -rf *.log *.pdf *.aux *.blg *.bbl *.out
