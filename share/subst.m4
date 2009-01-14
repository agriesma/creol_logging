dnl
dnl subst.m4 -- Expand MAP with a lazy compose operator.
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
***
*** Binding variables to values.
***
*** Uses MAP from prelude.
***
fmod CREOL-SUBST is
    protecting CREOL-DATATYPES .
    extending MAP{Vid, Data} * (sort Map{Vid,Data} to Subst,
                                sort Entry{Vid,Data} to Binding,
                                op empty : -> Map{Vid,Data} to noSubst) .

    vars A A' : Vid .
    vars D D' : Data .
    vars S1 S2  : Subst .

    *** Lazy composition operator for substitutions
    op _::_ : Subst Subst -> Subst .
    eq (S1 :: S2)[A] = if $hasMapping(S2, A) then S2[A] else S1[A] fi .

    --- Composition operater for substitutions
    ---
    --- Insert all bindings of S2 into S1, overriding the binding
    --- in S1.
    op compose : Subst Subst -> Subst .
    eq compose(S1, noSubst) = S1 .
    eq compose(noSubst, S2) = S2 .
    eq compose(S1, (S2, (A |-> D))) = compose(insert(A, D, S1), S2) .

    --- Remove all bindings of S2 from S1.
    op remove : Subst Subst -> Subst .
    eq remove(S1, noSubst) = S1 .
    eq remove(noSubst, S2) = S2 .
    eq remove((S1, (A |-> D)), (S2, (A |-> D'))) = remove(S1, S2) .
    eq remove(S1, (S2, (A |-> D'))) = remove(S1, S2) [owise] .
endfm
dnl
