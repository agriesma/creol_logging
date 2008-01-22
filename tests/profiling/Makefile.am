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

MOSTLYCLEANFILES	= *~
CLEANFILES		= *.prof
DISTCLEANFILES		= *.maude
MAINTAINERCLEANFILES	= Makefile.in

EXTRA_DIST	= generate.sh Philosophers.creol

SUFFIXES	= .maude .prof

CREOL_LIBRARY_PATH	= ${top_srcdir}/share
MAUDE_LIB		:= ${top_builddir}/share:${MAUDE_LIB}

export CREOL_LIBRARY_PATH MAUDE_LIB

check-local: Phil1.prof Phil2.prof

.maude.prof:
	${MAUDE} $< > $@

Phil1.maude: Philosophers.creol
	rm -f model.maude
	 ${top_builddir}/creolc/creolc -T maudemc -o model.maude $<
	$(SHELL) ${srcdir}/generate.sh model.maude $@
	rm -f model.maude

Phil2.maude: Philosophers.creol
	rm -f model.maude
	${top_builddir}/creolc/creolc -T maudemc -p devirt -o model.maude $<
	$(SHELL) ${srcdir}/generate.sh model.maude $@
	rm -f model.maude
