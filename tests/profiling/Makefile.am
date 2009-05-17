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

EXTRA_DIST	= benchmark.sh profile.sh \
		  Philosophers.creol Philosophers.tests

SUFFIXES	= .maude .prof

CREOL_LIBRARY_PATH	= $(top_srcdir)/share

PROFILE		= $(SHELL) $(srcdir)/profile.sh
BENCHMARK	= $(SHELL) $(srcdir)/benchmark.sh
CREOLC		= $(top_builddir)/creolc/creolc

export CREOL_LIBRARY_PATH

check-local: Phil1b.prof Phil1p.prof Phil2b.prof Phil2p.prof

.maude.prof:
	env MAUDE_LIB=$(top_builddir)/share:${top_srcdir}/share:$$MAUDE_LIB $(MAUDE) $< > $@

Phil1p.maude: Philosophers.creol Philosophers.tests $(srcdir)/profile.sh
	rm -f model.maude
	$(CREOLC) -T maude -m modelchecker -o model.maude $<
	$(PROFILE) model.maude $(srcdir)/Philosophers.tests $@
	rm -f model.maude

Phil2p.maude: Philosophers.creol Philosophers.tests $(srcdir)/profile.sh
	rm -f model.maude
	$(CREOLC) -T maude -m modelchecker -p devirt -o model.maude $<
	$(PROFILE) model.maude $(srcdir)/Philosophers.tests $@
	rm -f model.maude

Phil1b.maude: Philosophers.creol Philosophers.tests $(srcdir)/benchmark.sh
	rm -f model.maude
	$(CREOLC) -T maude -m modelchecker -o model.maude $<
	$(BENCHMARK) model.maude $(srcdir)/Philosophers.tests $@
	rm -f model.maude

Phil2b.maude: Philosophers.creol Philosophers.tests $(srcdir)/benchmark.sh
	rm -f model.maude
	$(CREOLC) -T maude -m modelchecker -p devirt -o model.maude $<
	$(BENCHMARK) model.maude $(srcdir)/Philosophers.tests $@
	rm -f model.maude
