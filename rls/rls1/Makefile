# (C) Copyright 2010, COQTAIL team
# 
# Project Info: http://sourceforge.net/projects/coqtail/
# 
# This library is free software; you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation; either version 2.1 of the License, or
# (at your option) any later version.
# 
# This library is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
# License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
# USA.

THEORIES = myReals
LIBTHEORIES = $(addprefix mytheories/, $(THEORIES))

LIBDIRS = $(LIBTHEORIES) Reals Complex Arith
INCLUDES = $(addprefix -I , $(LIBDIRS)) -I .

COQDEP = coqdep
COQDEPFLAGS = $(INCLUDES)
COQC = coqc
COQCFLAGS = $(INCLUDES)
COQDOC = coqdoc
COQDOCFLAGS = -d doc -g --utf8

SRC_V = $(shell find $(LIBDIRS) -name "*.v")
SRC_DOC = $(SRC_V:.v=.html)

THEORIES_V = $(shell find mytheories/ -name "*.v")
THEORIES_VO = $(THEORIES_V:.v=.vo)

REALS_V = $(shell find Reals/ -name "*.v")
REALS_VO = $(REALS_V:.v=.vo)

COMPLEX_V = $(shell find Complex/ -name "*.v")
COMPLEX_VO = $(COMPLEX_V:.v=.vo)

ARITH_V = $(shell find Arith/ -name "*.v")
ARITH_VO = $(ARITH_V:.v=.vo)

all: theories reals complex arith doc

reals: $(REALS_VO)

complex: $(COMPLEX_VO)

arith: $(ARITH_VO)

theories: $(THEORIES_VO)

doc: doc_dir $(SRC_DOC)
	sh alter_doc.sh

doc_dir:
	mkdir -p doc

clean:
	find . -name '*.vo' -o -name '*.glob' -o -name '*.v.d' | xargs rm -f
	rm -f doc/*.html doc/coqdoc.css
	rm -f dump.glob

.depend: $(SRC_V)
	$(COQDEP) $(COQDEPFLAGS) $(SRC_V) > .depend

%.vo %.glob: %.v
	$(COQC) $(COQCFLAGS) -dump-glob $*.glob $*

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -glob-from $*.glob -html $<

include .depend
