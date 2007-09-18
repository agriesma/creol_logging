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

AC_INIT([Creol Tools], 0.0g, kyas@ifi.uio.no, [creoltools])
AC_REVISION($Revision$)
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([creolc/Driver.ml])
AM_INIT_AUTOMAKE([1.9 dist-bzip2 readme-alpha check-news])
AC_PROG_MAKE_SET

dnl Record the date of release
RELEASE_DATE='2007-07-09'
AC_SUBST([RELEASE_DATE])

dnl Check for the tools needed to run the tests.
AC_PATH_PROG([M4], m4)
AC_PATH_PROG([AUTOM4TE], autom4te)
AC_PATH_PROG([DIFF], diff)

dnl Check for the tools needed to compile ocaml code.
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


dnl For documentation.
AC_CHECK_PROG([DOT], [dot], [dot], ['${top_srcdir}/missing dot'])

dnl Check for maude.
AC_CHECK_PROGS([MAUDE], [maude.linux maude.darwin maude],
	       ['${top_srcdir}/maude-sh'])

# Check whether the maude we found is usable.
if (${MAUDE} --version >/dev/null 2>&1 || exit)
then
(exit)
else
AC_MSG_WARN([Failed to execute maude (${MAUDE})

Maude has not been found or could not be executed.  Therefore, the test
suite will fail for all test cases during their execution in maude.  You
still can compile the compiler, however.  To rectify this problem, please
install Maude from <http://maude.cs.uiuc.edu/>.

If you are sure that you have maude installed, rerun $as_me with
--with-maude=/path/to/your/maude
])
fi

AC_MSG_CHECKING([for ocaml-libxml2 bindings])
ocamllibxml2=`$OCAMLFIND query libxml2 2>/dev/null`
if test "$?" = "0"
then
  AC_MSG_RESULT([yes])
  AC_MSG_NOTICE([Found XML library at $ocamllibxml2])
else
  AC_MSG_RESULT([no])
  AC_MSG_ERROR([ocaml-libxml2 cannot be found.

You have to install ocaml-libxml2 from
<http://heim.ifi.uio.no/~kyas/creoltools/> to compile the creoltools.
])
fi

AC_ARG_WITH([included-creol-mode],
    AS_HELP_STRING([--with-included-creol-mode],
       [Whether to use the included creol mode for emacs]),
    [if test "x$with_included_maude_mode" = "xyes" ; then 
       CREOL_MODE=creol-mode
     else
       CREOL_MODE=
     fi],
[CREOL_MODE=creol-mode])
AC_SUBST([CREOL_MODE])

AC_SUBST([MENHIR_FLAGS])
AC_SUBST([OCAMLC_FLAGS])
AC_SUBST([OCAMLOPT_FLAGS])
AC_SUBST([OCAMLFIND_FLAGS])
AC_SUBST([CREOL_VARIANTS])

AC_CONFIG_TESTDIR(tests, creolc)

dnl Configure the subdirectories.
AC_CONFIG_SUBDIRS([creol-mode])

AC_CONFIG_FILES([creolbug], [chmod +x creolbug])
AC_CONFIG_FILES([creolshell], [chmod +x creolshell])
AC_CONFIG_FILES([Makefile
		 creolc/Makefile
		 info/Makefile
		 share/Makefile
		 tests/atlocal
		 tests/Makefile])
AC_OUTPUT
