dnl configure.ac -- use autoconf to create configure from this file.
dnl
dnl This file is part of creolcomp
dnl
dnl Written and Copyright (c) 2007 by Marcel Kyas
dnl
dnl This program is free software; you can redistribute it and/or
dnl modify it under the terms of the GNU General Public License as
dnl published by the Free Software Foundation; either version 2 of the
dnl License, or (at your option) any later version.
dnl
dnl This program is distributed in the hope that it will be useful, but
dnl WITHOUT ANY WARRANTY; without even the implied warranty of
dnl MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
dnl General Public License for more details.
dnl
dnl You should have received a copy of the GNU General Public License
dnl along with this program; if not, write to the Free Software
dnl Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
dnl 02111-1307, USA.

AC_INIT([Creol Tools], 0.0e, kyas@ifi.uio.no, [creoltools])
AC_REVISION($Revision$)
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([creolc/Driver.ml])
AM_INIT_AUTOMAKE([1.9 dist-bzip2 readme-alpha check-news])
AC_PROG_MAKE_SET

dnl Record the date of release
RELEASE_DATE='2007-06-22'
AC_SUBST([RELEASE_DATE])

dnl Check for the tools needed to run the tests.
AC_PATH_PROG([M4], m4)
AC_PATH_PROG([AUTOM4TE], autom4te)
AC_PATH_PROG([DIFF], diff)

dnl Check for the tools needed to compile ocaml code.
AC_CHECK_PROG([OCAMLFIND], [ocamlfind], [ocamlfind], [])
if [ -z "$OCAMLFIND" ]
then
    AC_MSG_ERROR([ocamlfind is not installed.

You have to install findlib from <http://www.ocaml-programming.de/>
to compile the creoltools.  Alternatively, you can install the
godi distribution from <http://godi.ocaml-programming.de/> to satisfy
this dependency.
])
fi
AC_CHECK_PROG([OCAMLLEX], [ocamllex], [ocamllex], [])
if [ -z "$OCAMLLEX" ]
then
    AC_MSG_ERROR([ocamllex cannot be found.

You have to install the ocaml from <http://caml.inria.fr/> or
<http://godi.ocaml-programming.de/> to compile the creoltools.  If you have
godi installed, then ocamllex should be installed, too.
])
fi
AC_CHECK_PROG([MENHIR], [menhir], [menhir], [])
if [ -z "$MENHIR" ]
then
    AC_MSG_ERROR([menhir cannot be found.

You have to install menhir from <http://cristal.inria.fr/~fpottier/menhir/>
or from <http://godi.ocaml-programming.de/> to compile the creoltools.  If
you use godi, the godi_console can help you in installing menhir.
])
fi

dnl For documentation.
AC_CHECK_PROG([DOT], [dot], [dot], [missing])

AC_ARG_WITH([maude],
    AS_HELP_STRING([--with-maude=name],
       [Whether to use maude and which binary to use.]),
    [if test "x$with_maude" = "xyes" ; then 
       AC_CHECK_PROG([MAUDE], [maude], [maude], [:])
     elif test "x$with_maude" = "x$no" ; then
       MAUDE="${top_srcdir}/missing maude"
     else
       MAUDE=$with_maude
     fi],
[AC_CHECK_PROGS([MAUDE], [maude maude.linux maude.darwin],
		[${top_srcdir}/missing maude])])

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

dnl Check for the programs needed by the test-suite.
AC_ARG_WITH([included-maude-mode],
    AS_HELP_STRING([--with-included-maude-mode],
       [Whether to use the included maude mode for emacs]),
    [if test "x$with_included_maude_mode" = "xyes" ; then 
       MAUDE_MODE=maude-mode
     else
       MAUDE_MODE=
     fi],
[MAUDE_MODE=maude-mode])
AC_SUBST([MAUDE_MODE])

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

AC_CONFIG_TESTDIR(tests, creolc)

dnl Configure the subdirectories.
AC_CONFIG_SUBDIRS([creol-mode maude-mode xml])

AC_CONFIG_FILES([creolbug], [chmod +x creolbug])
AC_CONFIG_FILES([creolshell], [chmod +x creolshell])
AC_CONFIG_FILES([creolc/Version.ml])
AC_CONFIG_FILES([Makefile
		 creolc/Makefile
		 info/Makefile
		 share/Makefile
		 tests/atlocal
		 tests/Makefile])
AC_OUTPUT
