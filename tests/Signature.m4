dnl 
dnl Many tests are actually testing grammar, and for these we use
dnl m4 to generate the test templates.
dnl
changequote({|,|})
define(GRAMMAR_TEST,dnl
red in $1 : $2 .
red in $1 : upTerm($2) .
red in $1 : downTerm(upTerm($2), $3) .
)dnl
***
*** Signature.maude -- Test cases for the common signature.
***
*** Copyright (c) 2007
***
*** This program is free software; you can redistribute it and/or
*** modify it under the terms of the GNU General Public License as
*** published by the Free Software Foundation; either version 2 of the
*** License, or (at your option) any later version.
***
*** This program is distributed in the hope that it will be useful, but
*** WITHOUT ANY WARRANTY; without even the implied warranty of
*** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
*** General Public License for more details.
***
*** You should have received a copy of the GNU General Public License
*** along with this program; if not, write to the Free Software
*** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
*** 02111-1307, USA.
***

set show timing off .
set show advise off .
in datatypes
in interpreter


red in SUBST : insert("var1", bool(true), noSubst) .
red in SUBST : insert("var2", bool(false), insert("var1", bool(true), noSubst)) .
red in SUBST : insert("var2", bool(false), insert("var1", bool(true), noSubst)) ["var1"] .
red in SUBST : upTerm(insert("var1", bool(false), noSubst)) .
red in SUBST : downTerm(upTerm(insert("var1", bool(false), noSubst)),noSubst) .
red in SUBST : downTerm(upTerm(insert("var2", bool(true), insert("var1", bool(false), noSubst)) ["var1"]), null) .
red in SUBST : dom("var1", insert("var2", bool(true), insert("var1", bool(false), noSubst))) .

GRAMMAR_TEST(GUARDS, wait, noGuard)
GRAMMAR_TEST(GUARDS, bool(true), noGuard)
GRAMMAR_TEST(GUARDS, int(4) & int(5), noGuard)
GRAMMAR_TEST(GUARDS, int(4) & int(5) & wait, noGuard)
GRAMMAR_TEST(GUARDS, "test" ??, noGuard)
GRAMMAR_TEST(GUARDS, "test" ?? & "pest", noGuard)
GRAMMAR_TEST(GUARDS, {| "add" (int(4) # int(5)) & "label" ?? & wait & bool(true) & wait |}, noGuard)

GRAMMAR_TEST(STATEMENTS, "a" . 'a, "a")
GRAMMAR_TEST(STATEMENTS, "a" @ 'a, "a")
GRAMMAR_TEST(STATEMENTS, skip, "a" ::= "a")
GRAMMAR_TEST(STATEMENTS, "a" ::= "a", skip)
GRAMMAR_TEST(STATEMENTS, {| "var" ::= new 'C (int(5) # bool(true)) |}, skip)
GRAMMAR_TEST(STATEMENTS, 'm (emp : noAid), skip)
GRAMMAR_TEST(STATEMENTS, "o" . 'm (emp : noAid), skip)
GRAMMAR_TEST(STATEMENTS, "o" . 'm (bool(false) : noAid), skip)
GRAMMAR_TEST(STATEMENTS, "o" . 'm (emp : "r"), skip)
GRAMMAR_TEST(STATEMENTS, "o" . 'm (null : "r"), skip)
GRAMMAR_TEST(STATEMENTS, "l" ! 'm (emp), skip)
GRAMMAR_TEST(STATEMENTS, {| "l" ! 'm (null # null) |}, skip)
GRAMMAR_TEST(STATEMENTS, {| "l" ! "o" . 'm (null # "a") |}, skip)
GRAMMAR_TEST(STATEMENTS, {| (("l")?(noAid)) |}, skip)
GRAMMAR_TEST(STATEMENTS, (("l")?("l")), skip)
GRAMMAR_TEST(STATEMENTS, await ("test" ??) , skip)
GRAMMAR_TEST(STATEMENTS, await (("test" ??) & wait), skip)
GRAMMAR_TEST(STATEMENTS, await (("test" ??) & wait), skip)
GRAMMAR_TEST(STATEMENTS, return (emp), skip)
GRAMMAR_TEST(STATEMENTS, {| return ("a" # null # "c") |}, skip)
GRAMMAR_TEST(STATEMENTS, free (noAid), skip)
GRAMMAR_TEST(STATEMENTS, free ("a" , "b" , "c"), skip)
GRAMMAR_TEST(STATEMENTS, tailcall 'm (emp), skip)
GRAMMAR_TEST(STATEMENTS, {| tailcall 'm (null # "a") |}, skip)

GRAMMAR_TEST(STM-LIST, noStm, skip)
GRAMMAR_TEST(STM-LIST, skip, noStm)
GRAMMAR_TEST(STM-LIST, skip ; noStm, noStm)
GRAMMAR_TEST(STM-LIST, "var" ::= int(4) [] "var" ::= new 'C (null), noStm)
GRAMMAR_TEST(STM-LIST, "var" ::= int(4) [] "var" ::= new 'C (null) ||| skip, noStm)
GRAMMAR_TEST(STM-LIST, "var" ::= int(4) [] "var" ::= new 'C (null) ||| noStm ||| skip, noStm)

GRAMMAR_TEST(STM-LIST, idle, idle)
GRAMMAR_TEST(STM-LIST, {| (insert("var2", int(4), insert("var1", str("test"), noSubst)), ((("var" ::= int(4)) [] ("var" ::= new 'C (null))) ||| skip)) |}, noProc)
GRAMMAR_TEST(STM-LIST, noProc, idle)
GRAMMAR_TEST(STM-LIST, idle, noProc)
GRAMMAR_TEST(STM-LIST, {| (insert("var2", int(4), insert("var1", str("test"), noSubst)), ((("var" ::= int(4)) [] ("var" ::= new 'C (null))) ||| skip)) ++ idle |}, noProc)

GRAMMAR_TEST(OBJECT, {| < ob('object1) : 'class | Att: noSubst, Pr: idle, PrQ: noProc, Lcnt: 0 > |}, noObj)

GRAMMAR_TEST(COMMUNICATION, noMsg, noMsg)
GRAMMAR_TEST(COMMUNICATION, {| noQu |}, noQu)
GRAMMAR_TEST(COMMUNICATION, {| < ob('Ob1) : Qu | Size: 1, Dealloc: noDealloc , Ev: noMsg > |}, noQu)

fmod CREOL-LABEL-TEST is
  extending CREOL-DATA-SIG .
  extending COMMUNICATION .
  op label : Nat -> Label .
endfm

GRAMMAR_TEST(CREOL-LABEL-TEST, cont(label(1)), skip)
GRAMMAR_TEST(CREOL-LABEL-TEST, accept(label(1)), skip)
GRAMMAR_TEST(CREOL-LABEL-TEST, cont (label(5)), skip)
GRAMMAR_TEST(CREOL-LABEL-TEST, {| comp(label(5), emp) |}, noMsg)
GRAMMAR_TEST(CREOL-LABEL-TEST, {| invoc(ob('object1), label(5), 'method1, emp) |}, noMsg)

quit
