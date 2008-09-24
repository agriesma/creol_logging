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
CLEANFILES		= testsuite.log
DISTCLEANFILES		= atconfig atlocal
MAINTAINERCLEANFILES	= Makefile.in $(srcdir)/testsuite \
			  $(srcdir)/package.m4

AUTOTEST	= $(AUTOM4TE) --language=autotest
TESTSUITE	= $(srcdir)/testsuite

TESTPARTS	= $(srcdir)/testsuite.at

TESTFILES	= 

EXTRA_DIST	= $(srcdir)/atlocal.in \
		  $(srcdir)/package.m4 \
		  $(TESTPARTS) \
		  $(TESTSUITE) \
		  $(TESTFILES) \
		  $(srcdir)/Signature.m4 \
		  $(srcdir)/maude.sed

check-local: atconfig atlocal $(TESTSUITE)
	$(SHELL) $(TESTSUITE) $(TESTSUITEFLAGS)

installcheck-local: atconfig atlocal $(TESTSUITE)
	$(SHELL) $(TESTSUITE) AUTOTEST_PATH='$(bindir)' $(TESTSUITEFLAGS)

$(TESTSUITE): $(TESTPARTS) $(srcdir)/package.m4
	$(AUTOTEST) -I $(srcdir) $(srcdir)/testsuite.at -o $@.tmp
	mv $@.tmp $@

clean-local:
	test ! -f $(TESTSUITE) || \
	  $(SHELL) $(TESTSUITE) --clean $(TESTSUITEFLAGS)

$(srcdir)/package.m4: $(top_srcdir)/configure.ac
	@{ echo '# Signature of the current package.';			      \
	   echo 'm4_define([AT_PACKAGE_NAME],      [@PACKAGE_NAME@])';	      \
	   echo 'm4_define([AT_PACKAGE_TARNAME],   [@PACKAGE_TARNAME@])';     \
	   echo 'm4_define([AT_PACKAGE_VERSION],   [@PACKAGE_VERSION@])';     \
	   echo 'm4_define([AT_PACKAGE_STRING],    [@PACKAGE_STRING@])';      \
	   echo 'm4_define([AT_PACKAGE_BUGREPORT], [@PACKAGE_BUGREPORT@])';   \
	} > $(srcdir)/package.m4
