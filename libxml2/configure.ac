dnl configure.ac -- use autoconf to create configure from this file.
dnl
dnl This file is part of xml (OCaml bindings to libxml2)
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

AC_INIT([xml], 0.0b, kyas@ifi.uio.no)
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([XmlTextWriter.ml])
AM_INIT_AUTOMAKE([1.9 dist-bzip2 readme-alpha check-news])

dnl Check for the tools needed to build the text-reader and text-writer
dnl libraries
AC_PROG_CC
AC_PROG_RANLIB
AM_PATH_XML2(2.6.16)
AM_PATH_XSLT(1.1.11)

dnl Check for the tools needed to compile ocaml code.
AC_CHECK_PROG([OCAMLFIND], [ocamlfind], [ocamlfind], [false])
if test -z "$OCAMLFIND"
then
    AC_MSG_ERROR([ocamlfind is not installed.

You have to install findlib from <http://www.ocaml-programming.de/>
to compile the ocaml xml bindings.  Alternatively, you can install the
godi distribution from <http://godi.ocaml-programming.de/> to satisfy
this dependency.
])
fi

AC_CHECK_PROG([OCAMLMKLIB], [ocamlmklib], [ocamlmklib], [])
if test -z "$OCAMLMKLIB"
then
    AC_MSG_ERROR([ocamlmklib is not installed.

You have to install ocaml from <http://caml.inria.fr/>
to compile the ocaml xml bindings.  Alternatively, you can install the
godi distribution from <http://godi.ocaml-programming.de/> to satisfy
this dependency.
])
fi

dnl figure out the site-lib directory. The following is bogus...
OCAML_SITELIB=`ocamlfind printconf path`
OCAML_LDCONF=`ocamlfind printconf ldconf`

# This mess needs to be done to have ocamlfind cooperate with ocamlfind
# I think that this suck...
AC_ARG_ENABLE([make-install], [Do not use it, it may break make install!],
[if test "$enableval" = "no"
then
  OCAML_SITELIB='${libdir}'
  OCAML_LDCONF='${libdir}/ld.conf'
fi])

AC_SUBST([OCAML_LDCONF], [$OCAML_LDCONF])
AC_SUBST([OCAML_SITELIB], [$OCAML_SITELIB])

AC_SUBST([OCAMLC_FLAGS])
AC_SUBST([OCAMLOPT_FLAGS])

AC_OUTPUT([Makefile])
