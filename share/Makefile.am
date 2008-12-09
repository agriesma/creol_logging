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
DISTCLEANFILES		= creol-interpreter.maude \
			  creol-logginginterpreter.maude \
			  creol-modelchecker.maude \
			  creol-realtime.maude
MAINTAINERCLEANFILES	= Makefile.in

EXTRA_DIST		= README macros.m4 interpreter.m4 predicates.m4 \
			  configuration.m4 configuration2.m4 machine.m4 \
			  subst.m4 subst-2-2.m4 statements.m4 evaluation.m4
dist_pkgdata_DATA	= creol.xsd \
			  creol-datatypes.maude \
			  creol-loopmode.maude \
			  creol-metaexec.maude \
			  prelude.creol
pkgdata_DATA		= creol-interpreter.maude \
			  creol-logginginterpreter.maude \
			  creol-modelchecker.maude \
			  creol-realtime.maude

creol-interpreter.maude: $(srcdir)/interpreter.m4
	$(M4) -I$(srcdir) $(CREOL_VARIANT) $< > $@

creol-logginginterpreter.maude: $(srcdir)/interpreter.m4
	$(M4) -I$(srcdir) -DLOGGING $(CREOL_VARIANT) $< > $@

creol-modelchecker.maude: $(srcdir)/interpreter.m4
	$(M4) -I$(srcdir) -DMODELCHECK $(CREOL_VARIANT) $< > $@

creol-realtime.maude: ${srcdir}/interpreter.m4
	$(M4) -I$(srcdir) -DTIME $(CREOL_VARIANT) $< > $@

creol-interpreter.maude: ${srcdir}/macros.m4 ${srcdir}/machine.m4
creol-interpreter.maude: ${srcdir}/subst.m4
creol-interpreter.maude: ${srcdir}/statements.m4
creol-interpreter.maude: ${srcdir}/evaluation.m4
creol-interpreter.maude: ${srcdir}/configuration.m4
creol-interpreter.maude: ${srcdir}/configuration2.m4
creol-logginginterpreter.maude: ${srcdir}/macros.m4 ${srcdir}/machine.m4
creol-logginginterpreter.maude: ${srcdir}/subst.m4
creol-logginginterpreter.maude: ${srcdir}/statements.m4
creol-logginginterpreter.maude: ${srcdir}/evaluation.m4
creol-logginginterpreter.maude: ${srcdir}/configuration.m4
creol-logginginterpreter.maude: ${srcdir}/configuration2.m4
creol-modelchecker.maude: ${srcdir}/macros.m4  ${srcdir}/machine.m4
creol-modelchecker.maude: ${srcdir}/subst.m4
creol-modelchecker.maude: ${srcdir}/statements.m4
creol-modelchecker.maude: ${srcdir}/evaluation.m4
creol-modelchecker.maude: ${srcdir}/configuration.m4
creol-modelchecker.maude: ${srcdir}/predicates.m4
creol-realtime.maude: ${srcdir}/macros.m4 ${srcdir}/machine.m4
creol-realtime.maude: ${srcdir}/subst.m4
creol-realtime.maude: ${srcdir}/statements.m4
creol-realtime.maude: ${srcdir}/evaluation.m4
creol-realtime.maude: ${srcdir}/configuration.m4
