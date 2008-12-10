dnl
dnl Reimplementation of the CREOL KIND, 2007, 2008
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

*** The predicates we can define on configurations.
***
mod CREOL-PREDICATES is

  protecting CREOL-SIMULATOR .

  ops objcnt maxobjcnt minobjcnt : String Nat -> Prop .
  op hasvalue : Oid Vid Data -> Prop .

  var A : Vid .
  var D : Data .
  var C : String .
  var O : Oid .
  vars S S' L L' : Subst .
  var MM : MMsg .
  var P : Process .
  var Q : MProc .
  vars N N' : Nat .
  var c : Configuration .

  eq { c < C : Class | Inh: I:InhList`,' Param: AL:VidList`,' Att: S`,' Mtds: M:MMtd`,' Ocnt: N > } |= objcnt(C`,' N') = N == N' .
  eq { c < C : Class | Inh: I:InhList`,' Param: AL:VidList`,' Att: S`,' Mtds: M:MMtd`,' Ocnt: N > } |= maxobjcnt(C`,' N') = N <= N' .
  eq { c < C : Class | Inh: I:InhList`,' Param: AL:VidList`,' Att: S`,' Mtds: M:MMtd`,' Ocnt: N > } |= minobjcnt(C`,' N') = N >= N' .
  eq { c < O : C | Att: S`,' Pr: P`,' PrQ: Q`,' Ev: MM`,' Lcnt: N > } |= hasvalue(O`,' A`,' D) = D == S[A] .

endm
