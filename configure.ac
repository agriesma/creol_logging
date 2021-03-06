dnl configure.ac -- use autoconf to create configure from this file.
dnl
dnl This file is part of creolcomp
dnl
dnl Written and Copyright (c) 2007 by Marcel Kyas
dnl
dnl This program is free software; you can redistribute it and/or
dnl modify it under the terms of the GNU General Public License as
dnl published by the Free Software Foundation; either version 3 of the
dnl License, or (at your option) any later version.
dnl
dnl This program is distributed in the hope that it will be useful, but
dnl WITHOUT ANY WARRANTY; without even the implied warranty of
dnl MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
dnl General Public License for more details.
dnl
dnl You should have received a copy of the GNU General Public License
dnl along with this program.  If not, see <http://www.gnu.org/licenses/>.

AC_INIT([Creol Tools], [0.0m-git], [kyas@ifi.uio.no], [creoltools])
RELEASE='release'
RELEASE_DATE='2008-11-24'
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([creolc/Driver.ml])
AC_CONFIG_AUX_DIR([.])
AM_INIT_AUTOMAKE([1.9 dist-bzip2 readme-alpha check-news])
AC_SUBST([RELEASE])
AC_SUBST([RELEASE_DATE])

dnl Check for the tools needed to run the tests.
AC_CHECK_PROG([M4], [m4], [m4], [])
if test -z "$M4"
then
    AC_MSG_ERROR([m4 was not found.  You have to install m4 to compile the creoltools.])
fi

AC_CHECK_PROG([AUTOM4TE], [autom4te], [autom4te],
	      [[\${top_srcdir}/missing autom4te]])

dnl Check for the tools needed to compile ocaml code.
dnl
dnl The user may provide a path for ocamlfind
export OCAMLPATH
AC_SUBST([OCAMLPATH])

AC_CHECK_PROG([OCAMLFIND], [ocamlfind], [ocamlfind], [])
if test -z "$OCAMLFIND"
then
    AC_MSG_ERROR([ocamlfind was not found.

You have to install findlib from <http://www.ocaml-programming.de/>
to compile the creoltools.  Alternatively, you can install the
godi distribution from <http://godi.ocaml-programming.de/> to satisfy
this dependency.
])
fi

dnl We have found findlib, now we check for the version of findlib and
dnl ocamlc
AC_MSG_CHECKING([for version of findlib])
OCAMLFIND_VERSION=`$OCAMLFIND query -format '%v' findlib 2>/dev/null`
if test "$?" = "0"
then
  AC_MSG_RESULT([$OCAMLFIND_VERSION])
else
  AC_MSG_RESULT([none found])
  AC_MSG_ERROR([findlib cannot determine its version.

This may indicate that your installation of findlib is faulty.
])
fi

AC_MSG_CHECKING([for version of ocaml])
OCAML_VERSION=`$OCAMLFIND ocamlc -version 2>/dev/null`
if test "$?" = "0"
then
  AC_MSG_RESULT([$OCAML_VERSION])
else
  AC_MSG_RESULT([none found])
  AC_MSG_ERROR([findlib cannot determine version of ocamlc

This may indicate that your installation of ocaml or findlib is faulty.
])
fi

AC_SUBST([OCAMLFIND_VERSION])
AC_SUBST([OCAML_VERSION])

dnl If this test fails, we are on a platform which we do not support,
dnl because ocamllex is part of the ocaml distribution, and ocamlfind
dnl should depend on ocaml and friends!
AC_CHECK_PROGS([OCAMLLEX], [ocamllex.opt ocamllex], [''])
if test -z "$OCAMLLEX"
then
    AC_MSG_ERROR([ocamllex was not found.

This may indicate that your ocaml installation is faulty.
])
fi

AC_CHECK_PROG([MENHIR], [menhir], [menhir], [''])
if test -z "$MENHIR"
then
    AC_MSG_ERROR([menhir was not found.

You have to install menhir.  If you have installed menhir in a non-standard
place, rerun this script with 'MENHIR=/path/to/menhir'.  Otherwise, consult
INSTALL on obtaining and installing menhir.
])
fi

AC_SUBST([MENHIR_FLAGS])
AC_SUBST([OCAMLCFLAGS])
AC_SUBST([OCAMLOPTFLAGS])
AC_SUBST([OCAMLFINDFLAGS])
AC_SUBST([CREOL_VARIANTS])

dnl Check for maude.
AC_CHECK_PROGS([MAUDE], [maude.linux maude.linux64 maude.darwin maude],
	       [[\${abs_top_srcdir}/maude-sh]])

dnl Check whether the maude we found is usable.
AC_MSG_CHECKING([for version of maude])
MAUDE_VERSION=`${MAUDE} --version 2>/dev/null` 
if test "$?" = "0"
then
  AC_MSG_RESULT([$MAUDE_VERSION])
else
AC_MSG_WARN([Failed to execute maude (${MAUDE})

Maude has not been found or could not be executed.  Therefore, the test
suite will fail for all test cases during their execution in maude.  You
still can compile the compiler, however.  To rectify this problem, please
install Maude from <http://maude.cs.uiuc.edu/>.

If you are sure that you have maude installed, rerun $as_me with
MAUDE=/path/to/your/maude
])
fi
AC_SUBST([MAUDE_VERSION])

if test -z "$OCAML_LIBXML2"
then
    for i in libxml2 ocaml-libxml2
    do
        AC_MSG_CHECKING([for $i bindings])
        OCAML_LIBXML2_VERSION=`$OCAMLFIND query -format '%v' $i 2>/dev/null`
        if test "$?" = "0"
        then
            AC_MSG_RESULT($OCAML_LIBXML2_VERSION)
            OCAML_LIBXML2="$i"
            break
        else
            AC_MSG_RESULT([no])
        fi
    done
else
    OCAML_LIBXML2_VERSION=`$OCAMLFIND query -format '%v' $i 2>/dev/null`
    if test "$?" = "0"
    then
        AC_MSG_RESULT($OCAML_LIBXML2_VERSION)
    else
        AC_MSG_RESULT([no])
        unset OCAML_LIBXML2
    fi
fi

if test -z "$OCAML_LIBXML2"
then
    AC_MSG_ERROR([ocaml-libxml2 cannot be found.

You have to install ocaml-libxml2 from
<http://heim.ifi.uio.no/~kyas/creoltools/> to compile the creoltools.
])
fi

AC_SUBST([OCAML_LIBXML2])
AC_SUBST([OCAML_LIBXML2_VERSION])


AC_ARG_WITH([ounit],
    AS_HELP_STRING([--without-ounit],
		   [use oUnit and run unit tests (default=check).]),
[],
[with_ounit=check])

AC_MSG_CHECKING([for oUnit])
if test "$with_ounit" = "yes" || test "$with_ounit" = "check"
then
    OCAML_OUNIT_VERSION=`$OCAMLFIND query -format '%v' oUnit 2>/dev/null`
    if test "$?" = "0"
    then
        AC_MSG_RESULT($OCAML_OUNIT_VERSION)
        WITH_OUNIT="units"
    else
        AC_MSG_RESULT([no])
        WITH_OUNIT=""
    fi
else
    AC_MSG_RESULT([disabled])
    OCAML_UNIT_VERSION=""
    WITH_OUNIT=""
fi
AC_SUBST([OCAML_OUNIT_VERSION])
AC_SUBST([WITH_OUNIT])

dnl Check for literate programming tools.
AC_CHECK_PROG([DOT], [dot], [dot], [[\${top_srcdir}/missing dot]])
AC_CHECK_PROG([LATEX], [latex], [latex],
	      [[\${top_srcdir}/missing latex]])
AC_CHECK_PROG([PDFLATEX], [pdflatex], [pdflatex],
	      [[\${top_srcdir}/missing pdflatex]])
AC_CHECK_PROG([TEXI2DVI], [texi2dvi], [texi2dvi],
	      [[\${top_srcdir}/missing texi2dvi]])

AC_ARG_ENABLE([metatests],
  [AS_HELP_STRING([--with-metatests], [Run meta-execution tests.  Slow!])],
  [WITH_METATESTS=yes],
  [WITH_METATESTS=no])
AC_SUBST([WITH_METATESTS])

AC_ARG_ENABLE([profiling],
  [AS_HELP_STRING([--with-profiling], [Generate profiles.  Slow!])],
  [WITH_PROFILING=profiling],
  [WITH_PROFILING=""])
AC_SUBST([WITH_PROFILING])

AC_CONFIG_TESTDIR(tests, creolc)

AC_CONFIG_FILES([creolbug], [chmod +x creolbug])
AC_CONFIG_FILES([Makefile
		 creolc/Makefile
		 info/Makefile
		 share/Makefile
		 tests/atlocal
		 tests/Makefile
		 tests/profiling/Makefile
		 units/Makefile
])
AC_OUTPUT
