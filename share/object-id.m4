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
*** The sort of an object identifier.
***
fmod CREOL-OID is
    protecting NAT .
    protecting STRING .
    protecting CONVERSION .
    extending CREOL-DATA-SIG .
ifdef(`WITH_MAUDE_CONFIG',
`    extending CONFIGURATION .',
`    sort Oid .')

    subsort Oid < Data .

    --- Constructor of object names
    op ob(_) : String -> Oid [ctor `format' (d d ! o d)] .

    var B : String .
    var F : Nat .

    --- Create a new fresh name for an object
    op newId : String Nat -> Oid .
    eq newId(B, F)  = ob(B + string(F,10)) .

endfm

view Oid from TRIV to CREOL-OID is
  sort Elt to Oid .
endv

