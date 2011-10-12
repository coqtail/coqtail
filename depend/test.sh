./coqdep -R ~/svn/coqtail/src/ Coqtail -coqlib /usr/lib/coq/ -dumpgraph ~/svn/coqtail/src/Reals/RStirling.v > test.dot; dot -Tpdf test.dot -o test.pdf

