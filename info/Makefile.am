## Makefile.am - Use automake to create Makefile.in
#
# This file is part of creoltools
#
# Written and Copyright (c) 2005 by Marcel Kyas
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

info_TEXINFOS		= creoltools.texi

creoltools_TEXINFOS	= introduction.texi \
			  creoltut.texi \
			  creolexpr.texi \
			  creolcls.texi \
			  creolcomm.texi \
			  creolflow.texi \
			  creollib.texi \
			  creol.texi \
			  pragma.texi \
			  creolmc.texi \
			  creolrt.texi \
			  cmc.texi \
			  creolc.texi \
			  faq.texi \
			  bugs.texi \
			  bibliography.texi \
			  grammar.texi \
			  cmcgrammar.texi \
			  fdl.texi \
			  gpl.texi \
			  readme.texi \
			  install.texi

BUILT_SOURCES		= $(srcdir)/sorts.eps \
			  $(srcdir)/sorts.pdf \
			  $(srcdir)/sorts.png \
			  $(srcdir)/types.eps \
			  $(srcdir)/types.pdf \
			  $(srcdir)/types.png

EXTRA_DIST		= $(srcdir)/sorts.dot \
			  $(srcdir)/sorts.txt \
			  $(srcdir)/sorts.eps \
			  $(srcdir)/sorts.pdf \
			  $(srcdir)/sorts.png \
			  $(srcdir)/types.dot \
			  $(srcdir)/types.txt \
			  $(srcdir)/types.eps \
			  $(srcdir)/types.pdf \
			  $(srcdir)/types.png

MOSTLYCLEANFILES	= *~ *.cps
CLEANFILES		=
DISTCLEANFILES		=
MAINTAINERCLEANFILES	= $(srcdir)/sorts.eps \
			  $(srcdir)/sorts.pdf \
			  $(srcdir)/sorts.png

.dot.eps:
	${DOT} -T ps2 -o $@ $<

.eps.pdf:
	ps2pdf14 $< $@

.dot.png:
	${DOT} -T png -o $@ $<

creoltools.dvi: $(creoltools_TEXINFOS) sorts.eps
creoltools.pdf: $(creoltools_TEXINFOS) sorts.pdf
creoltools.info: sorts.txt
