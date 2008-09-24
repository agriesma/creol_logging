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
*** In Maude 2.3`,' MAP checks whether the variable is bound for each insert.
*** This check`,' however`,' is the main performance issue of the model
*** checker:  over 13% of the rewrites are for $hasMapping from MAP this
*** map implementation.  We could replace map with our own and making use
*** of the assumption`,' that insert behaves well in our case.
*** 
*** This is an experimental version`,' where we roll our own version of a
*** substitution.  It saves a lot of rewrites`,' but matching becomes much
*** more expensive with this version`,' which causes a substantial run-time
*** regression.
fmod CREOL-SUBST is
  protecting BOOL .
  protecting EXT-BOOL .
  protecting CREOL-DATATYPES .

  sort Binding Subst .
  subsort Binding < Subst .

  op _|->_ : Vid Data -> Binding [ctor] .
  op noSubst : -> Subst [ctor] .
  op _`,'_ : Subst Subst -> Subst [ctor assoc comm id: noSubst prec 121 `format' (d r os d)] .
  op undefined : -> [Data] [ctor] .
  
  vars A A' : Vid .
  vars D D' : Data .
  vars S1 S2  : Subst .

  op insert : Vid Data Subst -> Subst .
  eq insert(A`,' D`,' (S1`,' A |-> D')) =
     if $hasMapping(S1`,' A) then insert(A`,' D`,' S1)
     else (S1`,' A |-> D)
     fi .
  eq insert(A`,' D`,' S1) = (S1`,' A |-> D) [owise] .

  op $hasMapping : Subst Vid -> Bool .
  eq $hasMapping((S1`,' A |-> D)`,' A) = true .
  eq $hasMapping(S1`,' A) = false [owise] .

  *** Lazy composition operator for substitutions
  op _::_ : Subst Subst -> Subst [strat (0)] .

  *** Get a value
  op _[_] : Subst Vid -> [Data] [prec 23] .
  eq (S1 :: (S2`,' A |-> D))[ A ] = D .
  eq ((S1`,' A |-> D) :: S2)[ A ] = D .
  eq (S1`,' A |-> D)[A] = D .
  eq S1[A] = undefined [owise] .

  *** Composition operater for substitutions
  op compose : Subst Subst -> Subst .
  eq compose(S1`,' noSubst) = S1 .
  eq compose(noSubst`,' S2) = S2 .
  eq compose(S1`,' (S2`,' (A |-> D))) = compose(insert(A`,' D`,' S1)`,' S2) .
endfm
