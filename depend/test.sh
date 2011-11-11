./coqdep -R ~/svn/coqtail/src/ Coqtail -coqlib /usr/lib/coq/ -dumpgraph ~/svn/coqtail/src/Reals/Dequa_examples.v > test.dot; tred < test.dot > test2.dot; dot -Tpdf test2.dot -o test.pdf

