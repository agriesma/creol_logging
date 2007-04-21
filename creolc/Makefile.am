## Makefile.am - Use automake to create Makefile.in
#
# This file is part of creoltools
#
# Written and Copyright (c) 2007 by Marcel Kyas
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as
# published by the Free Software Foundation; either version 2 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
# 02111-1307, USA.

# Findlib related
OCAMLPATH		= $(top_builddir)
export OCAMLPATH

# Subdirs
MOSTLYCLEANFILES	= *~ *.aux *.log
CLEANFILES		= *.cmi *.cmo *.cmx *.cma *.cmxa *.o *.tex
DISTCLEANFILES		= html-stamp
MAINTAINERCLEANFILES	= .depend $(BUILT_SOURCES)

EXTRA_DIST		= .depend Creol.mll Creol.mly

bin_PROGRAMS		= creolc creolc.opt

BUILT_SOURCES		= CreolLex.ml CreolParser.ml CreolParser.mli

creolc_SOURCES		= Version.ml Messages.ml \
			  Creol.mli Creol.ml \
			  CreolLex.ml CreolLex.mli \
			  CreolParser.mli CreolParser.ml \
			  CreolIO.mli CreolIO.ml \
			  Driver.ml

creolc_opt_SOURCES	= $(creolc_SOURCES)

OCAMLC_FLAGS		+=
OCAMLOPT_FLAGS		+= -w a
OCAMLFIND_FLAGS		+= -package unix,xml

SUFFIXES = .ml .mli .mll .mly .cmi .cmo .cmx .cma .cmax

creolc: $(patsubst %.ml, %.cmo, $(patsubst %.mli, %.cmi, $(creolc_SOURCES)))
	$(OCAMLFIND) ocamlc $(OCAMLFIND_FLAGS) $(OCAMLC_FLAGS) -linkpkg -o $@ $(filter %.cmo, $^)

creolc.opt: $(patsubst %.ml, %.cmx, $(patsubst %.mli, %.cmi, $(creolc_SOURCES)))
	$(OCAMLFIND) ocamlopt $(OCAMLFIND_FLAGS) $(OCAMLOPT_FLAGS) -linkpkg -o $@ $(filter %.cmx, $^)

.PRECIOUS: *.cmo *.cmi *.cmx
.ml.cmo:
	$(OCAMLFIND) ocamlc $(OCAMLFIND_FLAGS) $(OCAMLC_FLAGS) -o $@ -c $<

.mli.cmi:
	$(OCAMLFIND) ocamlc $(OCAMLFIND_FLAGS) $(OCAMLC_FLAGS) -o $@ -c $<

.ml.cmx:
	$(OCAMLFIND) ocamlopt $(OCAMLFIND_FLAGS) $(OCAMLOPT_FLAGS) -o $@ -c $<

# We must make sure that Creol.cmi is build before CreolParser.ml, but we
# do not want that CreolParser.ml depends on Creol.cmi, because then the
# end user needs to have menhir installed in order to rebuild the parser
# sources.  We build Creol.cmi by hand here.
#
# The interface in Creol.mli depends on the xml sub-package.  Unfortunately,
# Makefile depends on .depend, which depends on CreolParser.ml, which
# depends on Creol.mli, and therefore, Creol.cmi cannot be built.
# With this rule we make sure that the libxml2 subpackage is built before
# we generate the version of Creol.cmi needed by menhir to type-check
# CreolParser.ml.  Messy, uhm?
#
CreolParser.ml CreolParser.mli: Creol.mly
	( cd ${top_builddir}/xml && make )
	$(OCAMLFIND) ocamlc $(OCAMLFIND_FLAGS) $(OCAMLC_FLAGS) -o Creol.cmi -c ${srcdir}/Creol.mli
	rm -f CreolParser.conflicts
	$(MENHIR) $(MENHIR_FLAGS) --base CreolParser --infer $<

CreolLex.ml: Creol.mll
	$(OCAMLLEX) -o $@ $<

distclean-local:
	test ! -d html || rm -rf html

.depend: ${srcdir}/Makefile.am $(creolc_SOURCES)
	( cd ${top_builddir}/xml && make )
	$(OCAMLFIND) ocamldep $(OCAMLFIND_FLAGS) $(OCAMLDEP_FLAGS) $(filter %.mli, $^) $(filter %.ml, $^) > $@

html-local: html-stamp

.PHONY: libxml
libxml:


html-stamp: ${srcdir}/Makefile.am $(creolc_SOURCES)
	test -d html || mkdir html
	$(OCAMLFIND) ocamldoc $(OCAMLFIND_FLAGS) -html -d html $(creolc_SOURCES)

CreolLex.cmo: CreolParser.cmi
include ${srcdir}/.depend
