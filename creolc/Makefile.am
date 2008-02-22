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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
# 02111-1307, USA.

# Subdirs
MOSTLYCLEANFILES	= *~ *.aux *.log *.out \
			  *.cma *.cmxa *.cmi *.cmo *.cmx *.o
CLEANFILES		=
DISTCLEANFILES		= Version.ml creolc.dvi creolc.pdf
MAINTAINERCLEANFILES	= .depend Lexer.ml Parser.ml Parser.mli 

EXTRA_DIST		= .depend Lexer.mll Parser.mly creol.sty creolc.tex

bin_PROGRAMS		= creolc creolc.opt

BUILT_SOURCES		= Version.ml Lexer.ml Parser.ml Parser.mli

creolc_SOURCES		= Version.ml Misc.ml Messages.ml Creol.ml \
			  Typing.ml \
			  TreeLower.ml \
			  TreeSSA.ml TreeFold.ml \
			  TreeDef.ml \
			  TreeLife.ml \
			  TreeFree.ml TreeBury.ml TreeDevirt.ml \
			  TreeTailcall.ml \
			  Lexer.ml Lexer.mli \
			  Parser.ml Parser.mli \
			  BackendCreol.ml BackendMaude.ml BackendXML.ml \
			  BackendDot.ml \
			  Passes.ml \
			  Driver.ml

creolc_cmi		= Lexer.cmi Parser.cmi

creolc_cmo		= Version.cmo Misc.cmo Messages.cmo Creol.cmo \
			  Typing.cmo TreeLower.cmo TreeSSA.cmo TreeFold.cmo \
			  TreeDef.cmo TreeLife.cmo TreeFree.cmo TreeBury.cmo \
			  TreeDevirt.cmo TreeTailcall.cmo \
			  Lexer.cmo Parser.cmo \
			  BackendCreol.cmo BackendMaude.cmo BackendXML.cmo \
			  BackendDot.cmo \
			  Passes.cmo Driver.cmo

creolc_opt_SOURCES	= $(creolc_SOURCES)

creolc_cmx		= Version.cmx Misc.cmx Messages.cmx Creol.cmx \
			  Typing.cmx TreeLower.cmx TreeSSA.cmx TreeFold.cmx \
			  TreeDef.cmx TreeLife.cmx TreeFree.cmx TreeBury.cmx \
			  TreeDevirt.cmx TreeTailcall.cmx \
			  Lexer.cmx Parser.cmx \
			  BackendCreol.cmx BackendMaude.cmx BackendXML.cmx \
			  BackendDot.cmx \
			  Passes.cmx Driver.cmx

# This is the subset for which we want to generate documentation.
creolc_DOCSOURCES	= Driver.ml Passes.ml Messages.ml \
			  Lexer.mll Parser.mly \
			  Creol.ml \
			  Typing.ml \
			  TreeLower.ml \
			  TreeSSA.ml \
			  TreeFold.ml \
			  TreeDef.ml \
			  TreeLife.ml \
			  TreeFree.ml \
			  TreeBury.ml \
			  TreeDevirt.ml \
			  TreeTailcall.ml \
			  BackendCreol.ml BackendMaude.ml BackendXML.ml \
			  BackendDot.ml \
			  Misc.ml

OCAMLCFLAGS		+= -g
OCAMLOPTFLAGS		+= -w a -noassert -unsafe -inline 10
OCAMLFINDFLAGS		+= -package "num unix libxml2 str"

# The compilers.
OCAMLC		= $(OCAMLFIND) ocamlc
OCAMLOPT	= $(OCAMLFIND) ocamlopt
OCAMLDEP	= $(OCAMLFIND) ocamldep

SVNVERSION = \
	if test -d ${top_srcdir}/.svn ; \
	then \
	    env LANG=C svn info ${top_srcdir} | env LANG=C LC_ALL=C ${AWK} 'BEGIN { FS=":" } ($$1 == "Last Changed Rev") { printf "svn (r%d)", $$2 ; }' ; \
	else \
	    echo -n "release" ; \
	fi

SVNDATE = \
	if test -d ${top_srcdir}/.svn ; \
	then \
	    env LANG=C svn info ${top_srcdir} | env LANG=C LC_ALL=C ${AWK} 'BEGIN { FS=":" } ($$1 == "Last Changed Date") { s = $$2; sub(/ /, "", s) ; sub(/ .+/, "", s); print s }' ; \
	else \
	    echo -n "${RELEASE_DATE}" ; \
	fi

SUFFIXES = .ml .mli .mll .mly .cmi .cmo .cmx

creolc: $(creolc_cmi) $(creolc_cmo)
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -linkpkg -o $@ $(creolc_cmo)

creolc.opt: $(creolc_cmi) $(creolc_cmx)
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -linkpkg -o $@ $(creolc_cmx)

.PRECIOUS: *.cmo *.cmi *.cmx
.ml.cmo:
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $< -o $@

.mli.cmi:
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c $< -o $@ 

.ml.cmx:
	$(OCAMLOPT) $(OCAMLFINDFLAGS) $(OCAMLOPTFLAGS) -c $< -o $@ 

# We must make sure that Creol.cmi is build before Parser.ml, but we
# do not want that Parser.ml depends on Creol.cmi, because then the
# end user needs to have menhir installed in order to rebuild the parser
# sources.  We build Creol.cmi by hand here.  Same goes for Messages.cmi.
#
# Nonetheless, we depend on the source files, since type inference needs
# to be redone after those files have been changed.
#
Parser.ml Parser.mli: Parser.mly Creol.ml Messages.ml
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c ${srcdir}/Messages.ml -o Messages.cmo
	$(OCAMLC) $(OCAMLFINDFLAGS) $(OCAMLCFLAGS) -c ${srcdir}/Creol.ml -o Creol.cmo
	rm -f Parser.conflicts
	$(MENHIR) $(MENHIR_FLAGS) --infer $<


Lexer.ml: Lexer.mll
	$(OCAMLLEX) -o $@ $<


all-local: depend-tmp version-tmp


${srcdir}/.depend: depend-tmp

.PHONY: depend-tmp
depend-tmp: ${srcdir}/Makefile.am $(creolc_SOURCES)
	@$(OCAMLDEP) $(OCAMLFINDFLAGS) $(OCAMLDEPFLAGS) $(creolc_SOURCES) \
		> depend-tmp
	@cmp -s depend-tmp $@ || \
		(echo "Updated dependencies." ; cp depend-tmp $@ )
	@rm -f depend-tmp


Version.ml: version-tmp

# Actually makes the file Version.ml
.PHONY: version-tmp
version-tmp:
	@(echo "(* This file is automatically generated.  Do not modify. *)" ; \
	 echo "let version = \"${VERSION}\"" ; \
	 echo "let release = \"`${SVNVERSION}`\"" ; \
	 echo "let package = \"${PACKAGE}\"" ; \
	 echo "let datadir = \"${pkgdatadir}\"" ; \
	 echo "let reldate = \"`${SVNDATE}`\"" ) > $@
	@cmp -s $@ Version.ml || \
	    (echo "Updating Version.ml" ; cp $@ Version.ml)
	@rm -f $@

# Literate programming, for documenting and explaining the compiler.
pdf-local: ${CREOLC_PDF}

creolc.pdf: creolc.tex code.tex
	${PDFLATEX} creolc
	${PDFLATEX} creolc
	${PDFLATEX} creolc

code.tex: ${srcdir}/Makefile.am ${creolc_DOCSOURCES}
	${OCAMLWEB} --no-preamble --no-index ${creolc_DOCSOURCES} -o $@

# Dependencies.
Lexer.cmo: Parser.cmi
-include ${srcdir}/.depend
