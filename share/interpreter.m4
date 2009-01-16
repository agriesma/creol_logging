include(macros.m4)dnl
dnl The usual header.
***
*** Reimplementation of the CREOL KIND
***
*** Copyright (c) 2007, 2008
***
*** Do NOT edit this file.  This file may be overwritten.  It has been
*** automatically generated from `interpreter.m4' using m4.
***
*** This file has been generated from interpreter.m4 ($Revision: 1812 $)
***
*** This program is free software; you can redistribute it and/or
*** modify it under the terms of the GNU General Public License as
*** published by the Free Software Foundation; either version 3 of the
*** License, or (at your option) any later version.
***
*** This program is distributed in the hope that it will be useful, but
*** WITHOUT ANY WARRANTY; without even the implied warranty of
*** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
*** General Public License for more details.
***
*** You should have received a copy of the GNU General Public License
*** along with this program.  If not, see <http://www.gnu.org/licenses/>.
***

ifdef(`MODELCHECK', `load model-checker .
')dnl
load creol-datatypes .


***************************************************************************
***
*** Signature of programs and states.
***
***************************************************************************

include(subst.m4)

include(class-id.m4)

include(object-id.m4)

include(statements.m4)

include(process.m4)

include(inherits.m4)

include(methods.m4)

include(`configuration.m4')

include(`evaluation.m4')

ifdef(`LOGGING', include(`replace.m4'))dnl

ifdef(`LOGGING', include(`rename.m4'))dnl

include(`machine.m4')

ifdef(`MODELCHECK', include(`predicates.m4'))dnl

eof
