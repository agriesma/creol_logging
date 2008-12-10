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
red in CREOL-SUBST : $hasMapping(insert("var2", bool(true), insert("var1", bool(false), noSubst)), "var1") .

GRAMMAR_TEST(DATA-BOOL, bool(true), null)
GRAMMAR_TEST(EXPRESSION, ?("test"), null)

GRAMMAR_TEST(STATEMENT, skip, assign("a" ; "a"))
GRAMMAR_TEST(STATEMENT, assign ("a" ; "a"), skip)
GRAMMAR_TEST(STATEMENT, {| new("var" ; "C" ; int(5) :: bool(true)) |}, skip)
GRAMMAR_TEST(STATEMENT, call("l" ; "this" ; "m" ; emp), skip)
GRAMMAR_TEST(STATEMENT, {| call("l" ; "this" ; "m" ; null :: null) |}, skip)
GRAMMAR_TEST(STATEMENT, {| call("l" ; "o" ; "m" ; null :: "a") |}, skip)
GRAMMAR_TEST(STATEMENT, {| get("l" ; noVid ) |}, skip)
GRAMMAR_TEST(STATEMENT, get ("l" ; "l" ), skip)
GRAMMAR_TEST(STATEMENT, await ?("test") , skip)
GRAMMAR_TEST(STATEMENT, return (emp), skip)
GRAMMAR_TEST(STATEMENT, {| return ("a" :: null :: "c") |}, skip)
GRAMMAR_TEST(STATEMENT, free ("a" ), skip)
GRAMMAR_TEST(STATEMENT, tailcall("this" ; "m" ; emp), skip)
GRAMMAR_TEST(STATEMENT, {| tailcall("this" ; "m" ; null :: "a") |}, skip)
GRAMMAR_TEST(STATEMENT, {| assert(bool(true)) |}, skip)
GRAMMAR_TEST(STATEMENT, {| failure(bool(true)) |}, skip)

GRAMMAR_TEST(STM-LIST, noStmt, skip)
GRAMMAR_TEST(STM-LIST, skip, noStmt)
GRAMMAR_TEST(STM-LIST, skip ; noStmt, noStmt)
GRAMMAR_TEST(STM-LIST, assign("var" ; int(4)) [] new("var" ; "C" ; null), noStmt)

GRAMMAR_TEST(PROCESS, idle, idle)
GRAMMAR_TEST(PROCESS-POOL, noProc, idle)
GRAMMAR_TEST(PROCESS-POOL, idle, noProc)

GRAMMAR_TEST(CONFIGURATION, {| noInh |}, noInh)
GRAMMAR_TEST(CONFIGURATION, {| "A" < emp > |}, noInh)
GRAMMAR_TEST(CONFIGURATION, {| "A" < emp > , "B" < "x" > |}, noInh)

GRAMMAR_TEST(CONFIGURATION, {| < ob("object1") : "Class" | Att: noSubst, Pr: idle, PrQ: noProc, Lcnt: 0 > |}, noObj)

GRAMMAR_TEST(CONFIGURATION, (none).Configuration, (none).Configuration)

mod CREOL-LABEL-TEST is
  extending CREOL-CONFIGURATION .
  op label : Nat -> Label .
endm

GRAMMAR_TEST(LABEL-TEST, $cont(label(1)), skip)
GRAMMAR_TEST(LABEL-TEST, $accept(label(1)), skip)
GRAMMAR_TEST(LABEL-TEST, $cont (label(5)), skip)
GRAMMAR_TEST(LABEL-TEST, {| comp(label(5), emp) |}, warning(""))
GRAMMAR_TEST(LABEL-TEST, {| invoc(ob("object1"), ob("object2"), label(5), "method1", emp) |}, warning(""))

quit
