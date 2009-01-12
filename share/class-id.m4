dnl
dnl class-id.m4 -- The sort of a class identifier.
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
*** The sort of a class identifier.
***
fmod CREOL-CID is
    protecting STRING .
ifdef(`WITH_UPDATE', ``    protecting NAT .
'')dnl
ifdef(`WITH_MAUDE_CONFIG',
`    protecting CONFIGURATION .',
`    sort Cid .')

ifdef(`WITH_UPDATE',
``    op class(_,_) : String Nat -> Cid [ctor] .'',
``    subsort String < Cid .'')

    op Class : -> Cid [ctor] .
    op Start : -> Cid [ctor] .
    op None : -> Cid [ctor] .
endfm

view Cid from TRIV to CREOL-CID is
  sort Elt to Cid .
endv
dnl
dnl Uniform representation for concrete class identifiers.
ifdef(`WITH_UPDATE',
  `define(`CLASS', `class($1, $2)')',
  `define(`CLASS', `$1')')dnl
