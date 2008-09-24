dnl
dnl subst-2-2.m4 -- The specification of the machine.
dnl
dnl Copyright (c) 2007, 2008
dnl
dnl The purpose of this file is to create the files `interpreter.maude'
dnl and `modelchecker.maude'.  These files have to be processed with
dnl m4, with either one of `CREOL' or `MODELCHECK' defined.
dnl
dnl See the lines below for its license
dnl
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

    *** Composition operater for substitutions
    op compose : Subst Subst -> Subst .
    eq compose(S1, noSubst) = S1 .
    eq compose(noSubst, S2) = S2 .
    eq compose(S1, (S2, (A |-> D))) = compose(insert(A, D, S1), S2) .
endfm
