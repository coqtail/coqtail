all : main todo

main :
	pdflatex main.tex

todo :
	grep "TODO" *.tex > TODO
	cat TODO
clean:
	rm -f *.aux *.log *.pdf TODO
