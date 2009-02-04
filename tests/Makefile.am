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
DISTCLEANFILES		= atconfig atlocal Signature.maude
MAINTAINERCLEANFILES	= Makefile.in $(srcdir)/testsuite \
			  $(srcdir)/package.m4

DIST_SUBDIRS		= profiling
SUBDIRS			= @WITH_PROFILING@

AUTOTEST		= $(AUTOM4TE) --language=autotest
TESTSUITE		= $(srcdir)/testsuite

TESTPARTS		= $(srcdir)/cmcvalid.at \
			  $(srcdir)/macros.at \
			  $(srcdir)/testsuite.at

TESTFILES	= examples/Alarmclock.creol examples/Alarmclock.maude \
		  examples/Alarmclock.out \
		  examples/AsyncLCR.creol examples/AsyncLCR.maude \
		  examples/AsyncLCR.out \
		  examples/AsyncSieveBuggy.creol \
		  examples/AsyncSieveBuggy.maude \
		  examples/AsyncSieveBuggy.out \
		  examples/AsyncSieve.creol \
		  examples/AsyncSieve.maude \
		  examples/AsyncSieve.out \
		  examples/BoundedBuffer.creol \
		  examples/BoundedBuffer.maude \
		  examples/BoundedBuffer.out \
		  examples/Buffer.creol examples/Buffer.maude \
		  examples/Buffer.out \
		  examples/CallAll.creol examples/CallAll.maude \
		  examples/CallAll.out \
		  examples/PeerToPeer.creol examples/PeerToPeer.maude \
		  examples/DiscreteTimeout.creol \
		  examples/DiscreteTimeout.maude \
		  examples/DiscreteTimeout.out \
		  examples/Fibonacci.creol examples/Fibonacci.maude \
		  examples/Fibonacci.out \
		  examples/Hello.creol examples/Hello.maude \
		  examples/Hello.out \
		  examples/HollywoodBuffer.creol \
		  examples/HollywoodBuffer.maude \
		  examples/HollywoodBuffer.out \
		  examples/PeerToPeer.creol examples/PeerToPeer.maude \
		  examples/PeerToPeer.out \
		  examples/PetersonLeader.creol \
		  examples/PetersonLeader.maude \
		  examples/PetersonLeader.out \
		  examples/PetersonLeader-cmc.out \
		  examples/Philosophers.creol \
		  examples/Philosophers.maude examples/Philosophers.out \
		  examples/SantaClaus.creol examples/SantaClaus.maude \
		  examples/SantaClaus.out \
		  examples/Sensors.creol examples/Sensors.maude \
		  examples/Sensors.out \
		  examples/Sieve.creol examples/Sieve.maude \
		  examples/Sieve.out \
		  examples/SingleCellBuffer.creol \
		  examples/SingleCellBuffer.maude \
		  examples/SingleCellBuffer.out \
		  language/Float.creol language/Float.maude \
		  language/Float.out \
		  language/Pair.creol language/Pair.maude language/Pair.out \
		  language/Inheritance.creol language/Inheritance.maude \
		  language/Inheritance.out \
		  language/Diamond.creol language/Diamond.maude \
		  language/Diamond.out \
		  language/Deadlock.creol language/Deadlock.maude \
		  language/Deadlock.out \
		  language/Map.creol language/Map.maude language/Map.out \
		  language/MultiCast.creol language/MultiCast.maude \
		  language/MultiCast.out \
		  language/MutRec.creol language/MutRec.maude \
		  language/MutRec.out \
		  language/MutRec2.creol language/MutRec2.maude \
		  language/MutRec2.out \
		  language/ReleaseWeirdness.creol \
		  language/ReleaseWeirdness.maude \
		  language/ReleaseWeirdness.out \
		  language/StackCheck.creol language/StackCheck.maude \
		  language/StackCheck.out \
		  language/StackGarbage.creol language/StackGarbage.maude \
		  language/StackGarbage.out \
		  language/Interleave.creol language/Interleave.maude \
		  language/Interleave.out \
		  language/While.creol language/While.maude \
		  language/While.out \
		  syntax/AttrDecl.creol \
		  syntax/MissingEnd.creol \
		  syntax/MissingEnd2.creol \
		  syntax/MissingEnd3.creol \
		  syntax/MissingEnd4.creol \
		  syntax/MissingEnd5.creol \
		  syntax/StrayChar.creol \
		  typecheck/Ambiguous.creol typecheck/Ambiguous2.creol \
		  typecheck/Ambiguous3.creol typecheck/Ambiguous4.creol \
		  typecheck/Ambiguous5.creol typecheck/Ambiguous6.creol \
		  typecheck/Ambiguous7.creol typecheck/Ambiguous8.creol \
		  typecheck/Contracts.creol typecheck/Cyclic.creol \
		  typecheck/Cyclic2.creol typecheck/Cyclic3.creol \
		  typecheck/Cyclic4.creol typecheck/CyclicClass.creol \
		  typecheck/ExprFailure.creol typecheck/If.creol \
		  typecheck/Implements.creol typecheck/Implements2.creol \
		  typecheck/Missing.creol typecheck/Missing2.creol \
		  typecheck/Missing3.creol \
		  typecheck/Nat.creol typecheck/Nat2.creol \
		  typecheck/Nat3.creol typecheck/Nat4.creol \
		  typecheck/Nil.creol typecheck/Nil2.creol \
		  typecheck/Nil3.creol \
		  typecheck/Set.creol typecheck/Set2.creol \
		  typecheck/Set3.creol typecheck/Set4.creol \
		  typecheck/Set5.creol typecheck/Set6.creol \
		  typecheck/Set7.creol \
		  typecheck/Future.creol typecheck/Future2.creol \
		  typecheck/Future3.creol typecheck/Future4.creol \
		  typecheck/Future5.creol \
		  typecheck/Map.creol typecheck/Map2.creol \
		  typecheck/Map3.creol typecheck/Map4.creol \
		  typecheck/New.creol typecheck/New2.creol \
		  typecheck/New3.creol typecheck/New4.creol \
		  typecheck/New5.creol typecheck/New6.creol \
		  typecheck/Inherits.creol \
		  devirt/Devirt.creol devirt/Devirt.xml \
		  bury/Assign.creol bury/Assign.xml \
		  bury/If.creol bury/If.xml \
		  free/Async.creol free/Async.xml \
		  free/AsyncRepl.creol free/AsyncRepl.xml \
		  free/AsyncAwaitRepl.creol free/AsyncAwaitRepl.xml \
		  free/AsyncAwait.creol free/AsyncAwait.xml \
		  free/AsyncChoice.creol free/AsyncChoice.xml \
		  free/AsyncAnon.creol free/AsyncAnon.xml \
		  free/LocalAsync.creol free/LocalAsync.xml \
		  free/If.creol free/If.xml \
		  free/Choice.creol free/Choice.xml \
		  tailcall/StaticTail.creol tailcall/StaticTail.xml \
		  tailcall/Tailcall.creol tailcall/Tailcall.xml \
		  into-ssa/Assign.creol into-ssa/Assign.xml \
		  split-ass/Assign.creol split-ass/Assign.xml \
		  Datatypes.maude Datatypes.out \
		  Signature.out \
		  Interpreter.maude Interpreter.out \
		  MetaExec.maude MetaExec.out \
		  modelchecker/ModelChecker.maude \
		  modelchecker/ModelChecker.out \
		  modelchecker/MC3Phil.creol modelchecker/MC3Phil.maude \
		  modelchecker/MC3Phil.out modelchecker/MC3PhilTest.maude \
		  modelchecker/MC4Phil.creol modelchecker/MC4Phil.maude \
		  modelchecker/MC4PhilTest.maude modelchecker/MC5Phil.creol \
		  modelchecker/MC5Phil.maude modelchecker/MC5PhilTest.maude

EXTRA_DIST	= $(srcdir)/atlocal.in \
		  $(srcdir)/package.m4 \
		  $(TESTPARTS) \
		  $(TESTSUITE) \
		  $(TESTFILES) \
		  $(srcdir)/Signature.m4 \
		  $(srcdir)/maude.sed

check-local: atconfig atlocal $(TESTSUITE) Signature.maude
	$(SHELL) $(TESTSUITE) $(TESTSUITEFLAGS)

installcheck-local: atconfig atlocal $(TESTSUITE) Signature.maude
	$(SHELL) $(TESTSUITE) AUTOTEST_PATH='$(bindir)' \
	  CREOL_LIBRARY_PATH="$(DESTDIR)$(pkgdatadir)" $(TESTSUITEFLAGS)


Signature.maude: $(srcdir)/Signature.m4
	m4 $< > $@

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
