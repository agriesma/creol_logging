dnl
dnl methods.m4 -- Declare methods
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
*** A method declaration
***
fmod CREOL-METHOD is
  protecting CREOL-STM-LIST .
  sort Method .

  op <_: Method | Param:_, Att:_, Code:_> : 
    String VidList Subst StmtList -> Method [ctor
      `format' (c ! oc o d sc o d sc o d sc o c o)] .

endfm

view Method from TRIV to CREOL-METHOD is
  sort Elt to Method .
endv
