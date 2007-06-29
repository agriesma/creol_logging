## Makefile.am - Use automake to create Makefile.in
#
# This file is part of creolcomp
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
export OCAMLPATH

# OCaml compilers.
OCAMLC			= $(OCAMLFIND) ocamlc
OCAMLCP			= $(OCAMLFIND) ocamlcp
OCAMLOPT		= $(OCAMLFIND) ocamlopt
OCAMLDEP		= $(OCAMLFIND) ocamldep
OCAMLDOC		= $(OCAMLFIND) ocamldoc

MOSTLYCLEANFILES	= *~ *.aux *.log
CLEANFILES		= *.cmi *.cmo *.cmx *.cma *.cmxa *.o *.tex \
			  dllxml.so xml.a libxml.a xml-stamp
DISTCLEANFILES		= META
MAINTAINERCLEANFILES	= .depend Makefile.in configure Version.ml \
			  depcomp missing install-sh aclocal.m4 \
			  xml.spec

EXTRA_DIST		= .depend META.in

BUILT_SOURCES		= META

noinst_LIBRARIES	= libxml_stubs.a

libxml_stubs_a_SOURCES	= xml_helpers.c xml_helpers.h xmld_stubs.c \
			  xmlr_stubs.c xmlw_stubs.c xslt_stubs.c \
			  Xml.ml XmlTextReader.ml XmlTextWriter.ml \
			  Xslt.ml
AM_CPPFLAGS		= $(XML_CPPFLAGS) $(XSLT_CPPFLAGS) -I`ocamlc -where` \
			  -DCAML_NAME_SPACE


# This probably works only with gcc.  It is not clear how we should handle
# position independend code (PIC) in a portable manner.
#
# i386 does not seem to have the stubs compiled as PIC.
# x86_64 insists on having PIC and accepts both -fpic and -fPIC
# Darwin wants us to use -fPIC only and wanrs about -fpic
# Solaris, HP-UX and others accept -fpic and -fPIC, but will use a
# small table with -fpic, which they prefer.

AM_CFLAGS		= -fPIC -DPIC

XML_DESTDIR		= `pwd`
OCAMLC_FLAGS		= -I . -I ${srcdir} -g -w y
OCAMLOPT_FLAGS		= -I . -I ${srcdir} -w a

all-local: xml.cma xml.cmxa dllxml.so libxml.a xml.a

.PRECIOUS: *.cmo *.cmi *.cmx *.cma *.cmxa
.ml.cmo:
	$(OCAMLC) $(OCAMLC_FLAGS) -o $@ -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLC_FLAGS) -o $@ -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPT_FLAGS) -o $@ -c $<

dllxml.so libxml.a xml.a: $(filter %.o, $(patsubst %.c, %.o, $(libxml_stubs_a_SOURCES)))
	$(OCAMLMKLIB) -o xml $^ $(XML_LIBS) $(XSLT_LIBS)

xml.cma: $(filter %.cmo, $(patsubst %.ml, %.cmo, $(libxml_stubs_a_SOURCES)))
	$(OCAMLMKLIB) -o xml $^ $(XML_LIBS) $(XSLT_LIBS)

xml.cmxa: $(filter %.cmx, $(patsubst %.ml, %.cmx, $(libxml_stubs_a_SOURCES)))
	$(OCAMLMKLIB) -o xml $^ $(XML_LIBS) $(XSLT_LIBS)

META: $(srcdir)/META.in $(top_srcdir)/configure.ac
	rm -f META && sed -e s/@VERSION\@/$(VERSION)/g < $< > $@

.depend: $(oclvp_SOURCES) $(libxml_stubs_a_SOURCES) ${srcdir}/Makefile.am
	$(OCAMLDEP) $(OCAMLDEP_FLAGS) $(filter %.mli, $^) $(filter %.ml, $^) > $@

distclean-local:
	test ! -d html || rm -rf html

install-exec-local: META xml.cma xml.cmxa libxml.a dllxml.so xml.a \
		Xml.cmi XmlTextReader.cmi XmlTextWriter.cmi Xslt.cmi
	test -d $(DESTDIR)$$(ocamlfind printconf path) || \
		mkdir -p $(DESTDIR)$$(ocamlfind printconf path)
	test -d $(DESTDIR)$$(dirname $$(ocamlfind printconf ldconf)) || \
		mkdir -p $(DESTDIR)$$(dirname $$(ocamlfind printconf ldocnf))
	$(OCAMLFIND) install -destdir $(DESTDIR)$$(ocamlfind printconf path) \
		-ldconf $(DESTDIR)$$(ocamlfind printconf ldconf) \
		xml $^

uninstall-local:
	$(OCAMLFIND) remove xml

html-local: ${srcdir}/Makefile.am $(libxml_stubs_a_SOURCES)
	test ! -d html || rm -rf html
	mkdir html
	$(OCAMLDOC) $(OCAMLFIND_FLAGS) -html -d html -m A *.ml*
	date > $@



XmlTextReader.cmi XmlTextWriter.cmi: META

-include ${srcdir}/.depend
