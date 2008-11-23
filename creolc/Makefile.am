## Makefile.am - Use automake to create Makefile.in
#
# This file is part of creoltools
#
# Written and Copyright (c) 2007, 2008 by Marcel Kyas
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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
# 02111-1307, USA.

# Subdirs
MOSTLYCLEANFILES	= *~ *.aux *.log *.out *.toc \
			  *.cma *.cmxa *.cmi *.cmo *.cmx *.a *.o
CLEANFILES		= creolc.prof
DISTCLEANFILES		= .depend Version.ml Driver.ml \
			   creol.cma creol.a creol.cmxa \
			   creolcint.pdf creolcint.tex ocamldoc.sty
MAINTAINERCLEANFILES	= $(srcdir)/CreolCreolLexer.ml $(srcdir)/CreolCreolParser.ml \
			  $(srcdir)/CreolCreolParser.mli 

EXTRA_DIST		= $(srcdir)/CreolLexer.mll $(srcdir)/CreolParser.mly

bin_PROGRAMS		= creolc creolc.opt cmcvalid cmcvalid.opt

noinst_PROGRAMS		= creoltop

BUILT_SOURCES		= Version.ml Driver.ml $(srcdir)/CreolLexer.ml \
			  $(srcdir)/CreolParser.ml $(srcdir)/CreolParser.mli

creolc_SOURCES		= Version.ml \
			  Misc.ml \
			  Config.ml \
			  Messages.ml \
			  Creol.ml \
			  Typing.ml \
			  TreeFold.ml \
			  TreeExpand.ml \
			  TreeUnassert.ml \
			  TreeUnprove.ml \
			  TreeSplitAss.ml \
			  TreeSSA.ml \
			  TreeDef.ml \
			  TreeLife.ml \
			  TreeLift.ml \
			  TreeFree.ml \
			  TreeBury.ml \
			  TreeDevirt.ml \
			  TreeTailcall.ml \
			  CheckUseDef.ml \
			  CMCParser.ml \
			  CreolLexer.mli CreolLexer.ml \
			  CreolParser.mli CreolParser.ml \
			  BackendCreol.mli BackendCreol.ml \
			  BackendMaude.ml \
			  BackendXML.ml \
			  BackendDot.ml \
			  Passes.mli Passes.ml \
			  Driver.m4

creolc_cmo		= Version.cmo Misc.cmo Config.cmo Messages.cmo \
			  Creol.cmo \
			  BackendCreol.cmo BackendMaude.cmo \
			  BackendDot.cmo $(BACKEND_XML_CMO) \
			  Typing.cmo TreeExpand.cmo TreeLift.cmo TreeFold.cmo \
			  TreeUnassert.cmo TreeUnprove.cmo TreeSSA.cmo \
			  TreeDef.cmo TreeLife.cmo TreeFree.cmo TreeBury.cmo \
			  TreeDevirt.cmo TreeTailcall.cmo TreeSplitAss.cmo \
			  CheckUseDef.cmo \
			  CreolLexer.cmo CreolParser.cmo CMCParser.cmo \
			  Passes.cmo

creolc_opt_SOURCES	= $(creolc_SOURCES)

creolc_cmx		= Version.cmx Misc.cmx Config.cmx Messages.cmx \
			  Creol.cmx \
			  BackendCreol.cmx BackendMaude.cmx \
			  BackendDot.cmx $(BACKEND_XML_CMX) \
			  Typing.cmx TreeExpand.cmx TreeLift.cmx TreeFold.cmx \
			  TreeUnassert.cmx TreeUnprove.cmx TreeSSA.cmx \
			  TreeDef.cmx TreeLife.cmx TreeFree.cmx TreeBury.cmx \
			  TreeDevirt.cmx TreeTailcall.cmx TreeSplitAss.cmx \
			  CheckUseDef.cmx \
			  CreolLexer.cmx CreolParser.cmx CMCParser.cmx \
			  Passes.cmx

cmcvalid_SOURCES	= CMCValid.ml

cmcvalid_cmo		= CMCValid.cmo

cmcvalid_opt_SOURCES	= $(cmcvalid_SOURCES)

cmcvalid_cmx		= CMCValid.cmx

creoltop_SOURCES	=

# This is the subset for which we want to generate documentation.
creolc_DOCSOURCES	= $(srcdir)/Passes.ml $(srcdir)/Passes.mli \
			  $(srcdir)/Creol.ml \
			  $(srcdir)/Typing.ml \
			  $(srcdir)/TreeUnassert.ml \
			  $(srcdir)/TreeExpand.ml \
			  $(srcdir)/TreeLift.ml \
			  $(srcdir)/TreeSSA.ml \
			  $(srcdir)/TreeFold.ml \
			  $(srcdir)/TreeDef.ml \
			  $(srcdir)/TreeLife.ml \
			  $(srcdir)/TreeFree.ml \
			  $(srcdir)/TreeBury.ml \
			  $(srcdir)/TreeDevirt.ml \
			  $(srcdir)/TreeTailcall.ml \
			  $(srcdir)/CheckUseDef.ml \
			  $(srcdir)/BackendCreol.ml \
			  $(srcdir)/BackendCreol.mli \
			  $(srcdir)/BackendMaude.ml \
			  $(srcdir)/BackendXML.ml \
			  $(srcdir)/BackendDot.ml \
			  $(srcdir)/Misc.ml \
			  $(srcdir)/Messages.ml \
			  $(srcdir)/Config.ml 

OCAMLCFLAGS		+= -g
OCAMLOPTFLAGS		+= -w a -noassert -unsafe -inline 20
OCAMLFINDFLAGS		+= -package "num unix $(OCAML_LIBXML2) str"

# The compilers.
OCAMLC		= $(OCAMLFIND) ocamlc
OCAMLCP		= $(OCAMLFIND) ocamlcp
OCAMLOPT	= $(OCAMLFIND) ocamlopt
OCAMLDEP	= $(OCAMLFIND) ocamldep -I $(srcdir)
OCAMLDOC	= $(OCAMLFIND) ocamldoc

SVNVERSION = \
	if test -d $(top_srcdir)/.svn ; \
	then \
	    env LANG=C svn info $(top_srcdir) | env LANG=C LC_ALL=C $(AWK) 'BEGIN { FS=":" } ($$1 == "Last Changed Rev") { printf "svn (r%d)", $$2 ; }' ; \
	else \
	    echo -n "release" ; \
	fi

SVNDATE = \
	if test -d $(top_srcdir)/.svn ; \
	then \
	    env LANG=C svn info $(top_srcdir) | env LANG=C LC_ALL=C $(AWK) 'BEGIN { FS=":" } ($$1 == "Last Changed Date") { s = $$2; sub(/ /, "", s) ; sub(/ .+/, "", s); print s }' ; \
	else \
	    echo -n "$(RELEASE_DATE)" ; \
	fi

SUFFIXES = .a .ml .mli .mll .mly .cma .cmi .cmo .cmx .cmxa

creolc: creol.cma Driver.cmo
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -linkpkg -o $@ $^

creol.cma: $(creolc_cmo)
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -a -o $@ $^

creolc.opt: creol.cmxa Driver.cmx
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -linkpkg -o $@ $^

creolc.prof: Driver.ml $(creolc_SOURCES)
	make mostlyclean
	make OCAMLC="$(OCAMLCP)" creolc
	mv creolc creolc.prof
	make mostlyclean

creol.cmxa: $(creolc_cmx)
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -a -o $@ $^

cmcvalid: creol.cma $(cmcvalid_cmo)
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -linkpkg -o $@ $^

cmcvalid.opt: creol.cmxa $(cmcvalid_cmx)
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -linkpkg -o $@ $^

creoltop: creol.cma
	$(OCAMLFIND) ocamlmktop $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -linkpkg -o $@ creol.cma

# These generic rules compile an OCaml source file to an object file.
.PRECIOUS: *.cmo *.cmi *.cmx *.cma *a. *.cmxa
.ml.cmo:
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $< -o $@

.mli.cmi:
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $< -o $@ 

.ml.cmx:
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -c $< -o $@

$(srcdir)/CreolLexer.ml: $(srcdir)/CreolLexer.mll
	$(OCAMLLEX) -o $@ $<


# We must make sure that Creol.cmi and Mesages.cmi are built before
# CreolParser.ml, because we use the --infer flag during the compilation
# of CreolParser.ml.  We do not want that CreolParser.ml depends on Creol.cmi or
# Messages.cmi, because then compiling the project at the end user
# requires recompilation of CreolParser.ml, which only works if the end user
# has menhir installed.
#
# Nonetheless, we depend on the source files, since the parser should
# be checked when these headers change.
#
$(srcdir)/CreolParser.ml: $(srcdir)/CreolParser.mly $(srcdir)/Misc.ml $(srcdir)/Creol.ml \
	  $(srcdir)/Messages.ml
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $(srcdir)/Misc.ml -o Misc.cmi
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $(srcdir)/Messages.ml -o Messages.cmi
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $(srcdir)/Creol.ml -o Creol.cmi
	rm -f CreolParser.conflicts
	$(MENHIR) $(MENHIR_FLAGS) --infer --base $(srcdir)/CreolParser $<
	(t=`mktemp menhir.XXXXXXXX` && mv $(srcdir)/CreolParser.ml $$t && \
	sed 's,_menhir_shifted = [0123456789][0123456789]*\(.*\)$$,_menhir_shifted = max_int \1,g' $$t > $(srcdir)/CreolParser.ml && \
	rm $$t)

$(srcdir)/CreolParser.mli: $(srcdir)/CreolParser.ml
	@if test -f $@ ; \
	then \
	    touch $@ ; \
	else \
	    rm -f $(srcdir)/CreolParser.ml ; \
	    $(MAKE) $(AM_MAKEFLAGS) $(srcdir)/CreolParser.ml ; \
	fi

Driver.ml: $(srcdir)/Driver.m4 Makefile
	$(M4) $(BACKEND_XML) $< > $@

all-local: version-tmp


Version.ml: version-tmp

# Actually makes the file Version.ml
.PHONY: version-tmp
version-tmp:
	@(echo "(* This file is automatically generated.  Do not modify. *)" ; \
	 echo "let version = \"$(VERSION)\"" ; \
	 echo "let release = \"`$(SVNVERSION)`\"" ; \
	 echo "let package = \"$(PACKAGE)\"" ; \
	 echo "let datadir = \"$(pkgdatadir)\"" ; \
	 echo "let reldate = \"`$(SVNDATE)`\"" ) > $@
	@cmp -s $@ Version.ml || \
	    (echo "Updating Version.ml" ; cp $@ Version.ml)
	@rm -f $@


# Generate the api documentation.
#$(OCAMLDOC) $(OCAMLFINDFLAGS) -sort -intro $(srcdir)/intro.txt \
#-html -d html $(creolc_DOCSOURCES)
html-local: html-stamp

html-stamp: $(creolc_DOCSOURCES)
	@rm -f html-stamp
	@test -d html || mkdir -p html
	$(OCAMLDOC) $(OCAMLFINDFLAGS) -html -d html $(creolc_DOCSOURCES)
	@echo html-stamp > html-stamp

pdf-local: creolcint.pdf

creolcint.pdf: creolcint.tex
	$(PDFLATEX) creolcint
	$(PDFLATEX) creolcint
	$(PDFLATEX) creolcint

creolcint.tex: $(creolc_DOCSOURCES)
	$(OCAMLDOC) $(OCAMLFINDFLAGS) -latex -o creolcint.tex \
	  $(creolc_DOCSOURCES)

distclean-local:
	test ! -d html || rm -rf html
	test ! -f html-stamp || rm -f html-stamp


# Compute the dependencies
.depend: Makefile $(creolc_SOURCES:.m4=.ml) $(cmcvalid_SOURCES)
	$(OCAMLDEP) $(OCAMLFINDFLAGS) $(OCAMLDEPFLAGS) $^ | \
	  sed s,$(srcdir)/,,g > $@

# Dependencies.
CreolParser.cmi: CreolParser.mli
CreolLexer.cmi: CreolParser.cmi
CreolLexer.cmo CreolLexer.cmx: CreolLexer.cmi

-include .depend


# Count lines.
#
# Parameters are for a semi-detached project
# (Effort 3.0 1.12, Schedule 2.5 0.38)
#
# RELY Low 0.88
# DATA Low 0.94
# CPLX Nominal 1.0
# TIME Nominal 1.0
# STOR Nominal 1.0
# VIRT Nominal 1.0
# TURN Nominal 1.0
# ACAP Low 1.19
# AEXP Low 1.13
# PCAP Low 1.17
# VEXP High 0.9
# LEXP High 0.95
# MODP Very High 0.82
# TOOL High 0.91
# SCED High 1.04
#
# Total: 0.86
#
sloccount: Driver.ml Version.ml
	@if test "$(srcdir)" != "." ; then \
	  for i in $^ ; do cp $$i $(srcdir)/$$i ; done ; \
	fi
	@sloccount --effort 2.59 1.12 --schedule 2.5 0.35 --personcost 424000 \
	  $(srcdir)
	@if test "$(srcdir)" != "." ; then \
	  for i in $^ ; do rm $(srcdir)/$$i ; done ; \
	fi
