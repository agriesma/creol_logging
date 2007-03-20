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

MOSTLYCLEANFILES	= *~
CLEANFILES		= testsuite.log
DISTCLEANFILES		= atconfig atlocal
MAINTAINERCLEANFILES	= Makefile.in testsuite package.m4

AUTOTEST		= ${AUTOM4TE} --language=autotest
TESTSUITE		= ${srcdir}/testsuite

TESTFILES	= Datatypes.maude Datatypes.expected \
		  Signature.maude Signature.expected \
		  Interpreter.maude Interpreter.expected \
		  MetaExec.maude MetaExec.expected \
		  ModelChecker.maude ModelChecker.expected \
		  Deadlock.creol Deadlock.maude Deadlock.expected \
		  Alarmclock.creol Alarmclock.maude Alarmclock.expected \
		  AsyncLCR.creol AsyncLCR.maude AsyncLCR.expected \
		  Philosophers.creol Philosophers.maude Philosophers.expected \
		  Sieve.creol Sieve.maude Sieve.expected \
		  SingleCellBuffer.creol SingleCellBuffer.maude \
		  SingleCellBuffer.expected \
		  Fibonacci.creol Fibonacci.maude Fibonacci.expected \
		  SantaClaus.creol SantaClaus.maude SantaClaus.expected \
		  BoundedBuffer.creol BoundedBuffer.maude BoundedBuffer.expected

TESTPARTS	= 

EXTRA_DIST	= ${srcdir}/atlocal.in ${srcdir}/testsuite.at maude.sed \
		  package.m4 testsuite ${TESTPARTS} ${TESTFILES} \
		  Signature.m4

check-local: atconfig atlocal ${TESTSUITE} Signature.maude
	$(SHELL) $(TESTSUITE)

Signature.maude: ${srcdir}/Signature.m4
	m4 $< > $@

clean-local:
	rm -rf testsuite.dir

${TESTSUITE}: ${srcdir}/testsuite.at ${srcdir}/package.m4 ${TESTPARTS}
	  ${AUTOTEST} -I ${srcdir} $< -o $@.tmp 
	  mv $@.tmp $@

package.m4: ${top_srcdir}/configure.ac
	@{ echo '# Signature of the current package.';			      \
	   echo 'm4_define([AT_PACKAGE_NAME],      [@PACKAGE_NAME@])';	      \
	   echo 'm4_define([AT_PACKAGE_TARNAME],   [@PACKAGE_TARNAME@])';     \
	   echo 'm4_define([AT_PACKAGE_VERSION],   [@PACKAGE_VERSION@])';     \
	   echo 'm4_define([AT_PACKAGE_STRING],    [@PACKAGE_STRING@])';      \
	   echo 'm4_define([AT_PACKAGE_BUGREPORT], [@PACKAGE_BUGREPORT@])';   \
	} >$(srcdir)/package.m4
