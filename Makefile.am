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
#

# Subdirs
DIST_SUBDIRS		= share info creolc tests
SUBDIRS			= share info creolc tests

MOSTLYCLEANFILES	= *~
DISTCLEANFILES		= 
MAINTAINERCLEANFILES	= $(srcdir)/Makefile.in $(srcdir)/configure \
			  $(srcdir)/aclocal.m4 $(srcdir)/missing \
			  $(srcdir)/install-sh \
			  $(srcdir)/INSTALL \
			  $(srcdir)/creoltools.spec

bin_SCRIPTS		= creolshell creolbug

EXTRA_DIST		= creoltools.spec creoltools.spec.in

AM_MAKEINFOFLAGS = --no-headers --no-validate --no-split

$(srcdir)/INSTALL: $(top_srcdir)/info/install.texi
	rm -f $@
	$(MAKEINFO) $(AM_MAKEINFOFLAGS) $(MAKEINFOFLAGS) -o $@ \
	  $(top_srcdir)/info/install.texi

$(srcdir)/README: $(top_srcdir)/info/readme.texi
	rm -f $@
	$(MAKEINFO) $(AM_MAKEINFOFLAGS) $(MAKEINFOFLAGS) -o $@ \
	  $(top_srcdir)/info/readme.texi

$(srcdir)/creoltools.spec: $(srcdir)/creoltools.spec.in $(srcdir)/configure.ac
	rm -f $@
	sed "s/@VERSION\@/$(VERSION)/" < $(srcdir)/creoltools.spec.in > $@
