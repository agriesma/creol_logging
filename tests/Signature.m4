dnl 
dnl Many tests are actually testing grammar, and for these we use
dnl m4 to generate the test templates.
dnl
changequote({|,|})
define(GRAMMAR_TEST,dnl
red in CREOL-$1 : $2 .
red in CREOL-$1 : upTerm($2) .
red in CREOL-$1 : downTerm(upTerm($2), $3) .
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
load creol-datatypes
load creol-interpreter


red in CREOL-SUBST : insert("var1", bool(true), noSubst) .
red in CREOL-SUBST : insert("var2", bool(false), insert("var1", bool(true), noSubst)) .
red in CREOL-SUBST : insert("var2", bool(false), insert("var1", bool(true), noSubst)) ["var1"] .
red in CREOL-SUBST : upTerm(insert("var1", bool(false), noSubst)) .
red in CREOL-SUBST : downTerm(upTerm(insert("var1", bool(false), noSubst)),noSubst) .
red in CREOL-SUBST : downTerm(upTerm(insert("var2", bool(true), insert("var1", bool(false), noSubst)) ["var1"]), null) .
red in CREOL-SUBST : dom("var1", insert("var2", bool(true), insert("var1", bool(false), noSubst))) .

GRAMMAR_TEST(DATA-SIG, bool(true), null)
GRAMMAR_TEST(DATA-SIG, "test" ??, null)

GRAMMAR_TEST(STATEMENT, "a" . "a", "a")
GRAMMAR_TEST(STATEMENT, "a" @ "a", "a")
GRAMMAR_TEST(STATEMENT, skip, "a" ::= "a")
GRAMMAR_TEST(STATEMENT, "a" ::= "a", skip)
GRAMMAR_TEST(STATEMENT, {| "var" ::= new "C" (int(5) # bool(true)) |}, skip)
GRAMMAR_TEST(STATEMENT, "l" ! "m" (emp), skip)
GRAMMAR_TEST(STATEMENT, {| "l" ! "m" (null # null) |}, skip)
GRAMMAR_TEST(STATEMENT, {| "l" ! "o" . "m" (null # "a") |}, skip)
GRAMMAR_TEST(STATEMENT, {| (("l")?(noVid)) |}, skip)
GRAMMAR_TEST(STATEMENT, (("l")?("l")), skip)
GRAMMAR_TEST(STATEMENT, await ("test" ??) , skip)
GRAMMAR_TEST(STATEMENT, return (emp), skip)
GRAMMAR_TEST(STATEMENT, {| return ("a" # null # "c") |}, skip)
GRAMMAR_TEST(STATEMENT, free ("a" ), skip)
GRAMMAR_TEST(STATEMENT, tailcall "m" (emp), skip)
GRAMMAR_TEST(STATEMENT, {| tailcall "m" (null # "a") |}, skip)
dnl Should not be accepted, but is with an ambigous parse!
dnl GRAMMAR_TEST(STATEMENT, "l" ! "this" . "m" @ "C" ( emp ) , skip)

GRAMMAR_TEST(STM-LIST, noStm, skip)
GRAMMAR_TEST(STM-LIST, skip, noStm)
GRAMMAR_TEST(STM-LIST, skip ; noStm, noStm)
GRAMMAR_TEST(STM-LIST, "var" ::= int(4) [] "var" ::= new "C" (null), noStm)
GRAMMAR_TEST(STM-LIST, "var" ::= int(4) [] "var" ::= new "C" (null) ||| skip, noStm)
GRAMMAR_TEST(STM-LIST, "var" ::= int(4) [] "var" ::= new "C" (null) ||| skip ||| skip, noStm)

GRAMMAR_TEST(STM-LIST, idle, idle)
GRAMMAR_TEST(STM-LIST, {| (insert("var2", int(4), insert("var1", str("test"), noSubst)), ((("var" ::= int(4)) [] ("var" ::= new "C" (null))) ||| skip)) |}, noProc)
GRAMMAR_TEST(STM-LIST, noProc, idle)
GRAMMAR_TEST(STM-LIST, idle, noProc)
GRAMMAR_TEST(STM-LIST, {| (insert("var2", int(4), insert("var1", str("test"), noSubst)), ((("var" ::= int(4)) [] ("var" ::= new "C" (null))) ||| skip)) ++ idle |}, noProc)

GRAMMAR_TEST(CLASS, {| noInh |}, noInh)
GRAMMAR_TEST(CLASS, {| "A" < emp > |}, noInh)
GRAMMAR_TEST(CLASS, {| "A" < emp > ## "B" < "x" > |}, noInh)

GRAMMAR_TEST(OBJECT, {| < ob("object1") : "Class" | Att: noSubst, Pr: idle, PrQ: noProc, Dealloc: noDealloc, Ev: noMsg, Lcnt: 0 > |}, noObj)

GRAMMAR_TEST(COMMUNICATION, noMsg, noMsg)

fmod CREOL-LABEL-TEST is
  extending CREOL-DATA-SIG .
  extending CREOL-COMMUNICATION .
  op label : Nat -> Label .
endfm

GRAMMAR_TEST(LABEL-TEST, cont(label(1)), skip)
GRAMMAR_TEST(LABEL-TEST, accept(label(1)), skip)
GRAMMAR_TEST(LABEL-TEST, cont (label(5)), skip)
GRAMMAR_TEST(LABEL-TEST, {| comp(label(5), emp) |}, noMsg)
GRAMMAR_TEST(LABEL-TEST, {| invoc(ob("object1"), label(5), "method1", emp) |}, noMsg)

quit
