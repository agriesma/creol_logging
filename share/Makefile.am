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
CLEANFILES		= 
DISTCLEANFILES		=
MAINTAINERCLEANFILES	= Makefile.in

EXTRA_DIST		= README interpreter.m4
dist_pkgdata_DATA	= creol.xsd \
			  creol-datatypes.maude \
			  creol-interpreter.maude \
			  creol-metaexec.maude \
			  creol-modelchecker.maude \
			  creol-realtime.maude \
			  prelude.creol

creol-interpreter.maude: ${srcdir}/interpreter.m4
	$(M4) ${CREOL_VARIANT} $^ > $@

creol-modelchecker.maude: ${srcdir}/interpreter.m4
	$(M4) -DMODELCHECK ${CREOL_VARIANT} $^ > $@

creol-realtime.maude: ${srcdir}/interpreter.m4
	$(M4) -DTIME ${CREOL_VARIANT} $^ > $@
