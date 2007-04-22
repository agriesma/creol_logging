dnl configure.ac -- use autoconf to create configure from this file.
dnl
dnl This file is part of creoltools
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

AC_INIT([creol-isabelle], 0.0a, kyas@ifi.uio.no)
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR([Creol/Creol.thy])
AM_INIT_AUTOMAKE([1.9 dist-bzip2 readme-alpha check-news])
AC_PROG_LN_S

dnl Check for the tools for building the heap.
AC_PATH_PROG([ISATOOL], isatool)

dnl Output.
AC_OUTPUT([Makefile])
