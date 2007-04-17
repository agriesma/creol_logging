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

TESTFILES	= Datatypes.maude Datatypes.out \
		  Signature.maude Signature.out \
		  Interpreter.maude Interpreter.out \
		  MetaExec.maude MetaExec.out \
		  ModelChecker.maude ModelChecker.out \
		  Inheritance.creol Inheritance.maude Inheritance.out \
		  Diamond.creol Diamond.maude Diamond.out \
		  Deadlock.creol Deadlock.maude Deadlock.out \
		  Alarmclock.creol Alarmclock.maude Alarmclock.out \
		  AsyncLCR.creol AsyncLCR.maude AsyncLCR.out \
		  Philosophers.creol Philosophers.maude Philosophers.out \
		  Sieve.creol Sieve.maude Sieve.out \
		  SingleCellBuffer.creol SingleCellBuffer.maude \
		  SingleCellBuffer.out \
		  Fibonacci.creol Fibonacci.maude Fibonacci.out \
		  SantaClaus.creol SantaClaus.maude SantaClaus.out \
		  BoundedBuffer.creol BoundedBuffer.maude BoundedBuffer.out

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
