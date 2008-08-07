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
creoltools_TEXINFOS	= introduction.texi invocation.texi creol.texi \
			  cmc.texi creolc.texi creolshell.texi faq.texi \
			  bibliography.texi creoltut.texi \
			  creollib.texi creolmc.texi creolrt.texi \
			  grammar.texi fdl.texi gpl.texi install.texi

BUILT_SOURCES		= sorts.eps sorts.pdf sorts.png
EXTRA_DIST		= sorts.dot sorts.txt sorts.eps sorts.pdf sorts.png

MOSTLYCLEANFILES	= *~ *.cps
CLEANFILES		=
DISTCLEANFILES		=
MAINTAINERCLEANFILES	= sorts.eps sorts.pdf sorts.png

.dot.eps:
	${DOT} -T ps2 -o $@ $<

.eps.pdf:
	ps2pdf14 $< $@

.dot.png:
	${DOT} -T png -o $@ $<
