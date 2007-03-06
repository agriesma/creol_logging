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

AC_INIT(creolcomp, 0.0a, kyas@ifi.uio.no)
AC_REVISION($Revision$)
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([Driver.ml])
AM_INIT_AUTOMAKE([1.9 dist-bzip2 dist-zip readme-alpha check-news])
AC_PROG_MAKE_SET
AC_PROG_LN_S

dnl Record the date of release
RELEASE_DATE='2007-03-05'
AC_SUBST([RELEASE_DATE])

dnl Check for the tools needed to run the tests.
AC_PATH_PROG([M4], m4)
AC_PATH_PROG([AUTOM4TE], autom4te)
AC_PATH_PROG([DIFF], diff)

dnl See whether we have chcon in order to fix tests with selinux.
AC_PATH_PROG([CHCON], chcon)

dnl Check for the tools needed to compile ocaml code.
AC_CHECK_PROG([OCAMLC], [ocamlc], [ocamlc], [false])
AC_CHECK_PROG([OCAMLOPT], [ocamlopt], [ocamlopt], [echo])
AC_CHECK_PROG([OCAMLDEP], [ocamldep], [ocamldep], [false])
AC_CHECK_PROG([OCAMLDOC], [ocamldoc], [ocamldoc], [echo])
AC_CHECK_PROG([OCAMLLEX], [ocamllex], [ocamllex], [false])
AC_CHECK_PROG([OCAMLFIND], [ocamlfind], [ocamlfind], [false])
AC_CHECK_PROG([MENHIR], [menhir], [menhir], [echo])

dnl Configure for building the creol mode.
AM_PATH_LISPDIR

dnl Configure the XML Text reader and writer library.
AC_CONFIG_SUBDIRS([xml])

AC_CONFIG_TESTDIR(tests, source)
AC_OUTPUT([Makefile emacs/Makefile info/Makefile maude/Makefile
	   tests/atlocal tests/Makefile])
