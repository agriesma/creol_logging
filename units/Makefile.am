## Makefile.am - Use automake to create Makefile.in
#
# This file is part of creoltools
#
# Written and Copyright (c) 2007 by Marcel Kyas
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as
# published by the Free Software Foundation; either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

MOSTLYCLEANFILES	= *~ *.cma *.cmxa *.cmi *.cmo *.cmx *.o
CLEANFILES		= 
DISTCLEANFILES		= $(noinst_PROGRAMS) .depend
MAINTAINERCLEANFILES	= Makefile.in

EXTRA_DIST		=

# The compilers.
OCAMLC		= $(OCAMLFIND) ocamlc -I ../creolc
OCAMLOPT	= $(OCAMLFIND) ocamlopt -I ../creolc
OCAMLDEP	= $(OCAMLFIND) ocamldep -I $(srcdir)

OCAMLCFLAGS	+= -g
OCAMLOPTFLAGS	+= -w a
OCAMLFINDFLAGS	+= -package "num unix $(OCAML_LIBXML2) str oUnit"

SUFFIXES = .ml .mli .mll .mly .cmi .cmo .cmx

noinst_PROGRAMS		= unittests unittests.opt

unittests_SOURCES	= CreolTests.ml UnitTests.ml

unittests_opt_SOURCES	= $(unittests_SOURCES)

unittests_cmo		= CreolTests.cmo UnitTests.cmo

unittests_cmx		= CreolTests.cmx UnitTests.cmx

unittests: $(unittests_cmo)
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -linkpkg -o $@ creol.cma $(unittests_cmo)

$(unittests_cmo): ../creolc/creol.cma

unittests.opt: $(unittests_cmx)
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -linkpkg -o $@ creol.cmxa $(unittests_cmx)

$(unittests_cmx): ../creolc/creol.cmxa

# These generic rules compile an OCaml source file to an object file.
.PRECIOUS: *.cmo *.cmi *.cmx
.ml.cmo:
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $< -o $@

.mli.cmi:
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $< -o $@ 

.ml.cmx:
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -c $< -o $@

check-local: unittests
	unittests

# Dependencies.
.depend: Makefile $(unittests_SOURCES)
	$(OCAMLDEP) $(OCAMLFINDFLAGS) $(OCAMLDEPFLAGS) $^ | \
	  sed s,$(srcdir)/,,g > $@

-include .depend
