## Makefile.am - Use automake to create Makefile.in
#
# This file is part of oclvp
#
# Written and Copyright (c) 2005 by Marcel Kyas
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

info_TEXINFOS		= creoltools.texi
creoltools_TEXINFOS	= introduction.texi invocation.texi creol.texi \
			  cmc.texi creolc.texi creolshell.texi \
			  bibliography.texi \
			  fdl.texi gpl.texi

EXTRA_DIST		= sorts.dot
BUILT_SOURCES		=

MOSTLYCLEANFILES	= *~ *.cps
CLEANFILES		=
DISTCLEANFILES		=
MAINTAINERCLEANFILES	=

.dot.eps:
	${DOT} -Tps -o temp.ps $<
	cp temp.ps $@
	rm -f temp.ps

.dot.pdf:
	${DOT} -Tps -o temp.ps $<
	ps2pdf14 temp.ps $@
	rm -f temp.ps

.dot.png:
	${DOT} -Tpng -o $@ $<
