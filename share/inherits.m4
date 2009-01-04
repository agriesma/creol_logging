dnl
dnl inherits.m4 -- Declare what to inherit.
dnl
dnl Copyright (c) 2007, 2008
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
dnl
*** An inherits declaration
***
fmod CREOL-INHERIT is
  protecting CREOL-DATATYPES .
  sort Inh .

  op  _<_> : String  ExprList -> Inh [ctor prec 15] .

endfm

view Inh from TRIV to CREOL-INHERIT is
  sort Elt to Inh .
endv

