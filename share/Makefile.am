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

MOSTLYCLEANFILES	= *~
CLEANFILES		= 
DISTCLEANFILES		=
MAINTAINERCLEANFILES	= Makefile.in

EXTRA_DIST		= README interpreter.m4
dist_pkgdata_DATA	= creol.xsd \
			  creol-datatypes.maude \
			  creol-interpreter.maude \
			  creol-metaexec.maude \
			  creol-modelchecker.maude

creol-interpreter.maude: ${srcdir}/interpreter.m4
	$(M4) ${CREOL_VARIANTS} $^ > $@

creol-modelchecker.maude: ${srcdir}/interpreter.m4
	$(M4) -DMODELCHECK ${CREOL_VARIANTS} $^ > $@
