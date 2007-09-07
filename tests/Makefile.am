## Makefile.am - Use automake to create Makefile.in
#
# This file is part of oclvp
#
# Written and Copyright (c) 2005 by Marcel Kyas
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
MAINTAINERCLEANFILES	= Makefile.in testsuite package.m4

AUTOTEST		= ${AUTOM4TE} --language=autotest
TESTSUITE		= ${srcdir}/testsuite

EXAMPLES	= examples/Alarmclock.creol examples/Alarmclock.maude \
		  examples/Alarmclock.out \
		  examples/AsyncLCR.creol examples/AsyncLCR.maude \
		  examples/AsyncLCR.out \
		  examples/AsyncSieveBuggy.creol \
		  examples/AsyncSieveBuggy.maude \
		  examples/AsyncSieveBuggy.out \
		  examples/AuthorisationPolicies.creol \
		  examples/AuthorisationPolicies.maude \
		  examples/AuthorisationPolicies.out \
		  examples/BoundedBuffer.creol \
		  examples/BoundedBuffer.maude \
		  examples/BoundedBuffer.out \
		  examples/Fibonacci.creol examples/Fibonacci.maude \
		  examples/Fibonacci.out \
		  examples/PeerToPeer.creol examples/PeerToPeer.maude \
		  examples/PeerToPeer.out \
		  examples/Philosophers.creol \
		  examples/Philosophers.maude examples/Philosophers.out \
		  examples/SantaClaus.creol examples/SantaClaus.maude \
		  examples/SantaClaus.out \
		  examples/Sieve.creol examples/Sieve.maude \
		  examples/Sieve.out \
		  examples/SingleCellBuffer.creol \
		  examples/SingleCellBuffer.maude \
		  examples/SingleCellBuffer.out

TESTFILES	= Datatypes.maude Datatypes.out \
		  Signature.maude Signature.out \
		  Interpreter.maude Interpreter.out \
		  MetaExec.maude MetaExec.out \
		  ModelChecker.maude ModelChecker.out \
		  Inheritance.creol Inheritance.maude Inheritance.out \
		  Diamond.creol Diamond.maude Diamond.out \
		  Deadlock.creol Deadlock.maude Deadlock.out \
		  MutRec.creol MutRec.maude MutRec.out \
		  MutRec2.creol MutRec2.maude MutRec2.out \
		  Interleave.creol Interleave.maude Interleave.out \
		  MC3Phil.creol MC3Phil.maude MC3Phil.out MC3PhilTest.maude \
		  MC4Phil.creol MC4Phil.maude MC4PhilTest.maude \
		  MC5Phil.creol MC5Phil.maude MC5PhilTest.maude

TESTPARTS	= 

EXTRA_DIST	= ${srcdir}/atlocal.in ${srcdir}/testsuite.at maude.sed \
		  package.m4 testsuite ${TESTPARTS} $(EXAMPLES) ${TESTFILES} \
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
