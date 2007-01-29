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

AC_INIT(creolcomp, 0.0.0, kyas@ifi.uio.no)
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([Driver.ml])
AM_INIT_AUTOMAKE([1.9])
AC_PROG_MAKE_SET
AC_PROG_LN_S

dnl Check for the tools needed to build the text-reader and text-writer
dnl libraries
AC_PROG_CC
AC_PROG_RANLIB
AM_PATH_XML2(2.6.0)

dnl Check for the tools needed to run the tests.
AC_PATH_PROG([M4], m4)
AC_PATH_PROG([AUTOM4TE], autom4te)
AC_PATH_PROG([DIFF], diff)
AC_PATH_PROG([XMLLINT], xmllint)
AC_PATH_PROG([XMLCATALOG], xmlcatalog)

dnl See whether we have chcon in order to fix tests with selinux.
AC_PATH_PROG([CHCON], chcon)

dnl Check for the tools needed to compile ocaml code.
AC_CHECK_PROG([OCAMLC], [ocamlc], [ocamlc], [false])
AC_CHECK_PROG([OCAMLFIND], [ocamlfind], [ocamlfind], [false])
AC_CHECK_PROG([OCAMLMKLIB], [ocamlmklib], [ocamlmklib], [false])
AC_CHECK_PROG([OCAMLLEX], [ocamllex], [ocamllex], [false])
AC_CHECK_PROG([MENHIR], [menhir], [menhir], [false])

dnl figure out the site-lib directory. The following is bogus...
OCAML_LIBDIR='${libdir}/ocaml'
OCAML_SITELIB='${OCAML_LIBDIR}/site-lib'
AC_SUBST([OCAML_LIBDIR], [$OCAML_LIBDIR])
AC_SUBST([OCAML_SITELIB], [$OCAML_SITELIB])

dnl Check for the tools needed to build the documentation.
AC_PATH_PROG([OCAMLDOC], ocamldoc)
AC_PATH_PROG([OCAMLWEB], ocamlweb)

AC_CONFIG_TESTDIR(tests, source)
AC_OUTPUT([Makefile tests/atlocal tests/Makefile xml/Makefile])
