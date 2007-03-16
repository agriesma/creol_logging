dnl 
dnl Many tests are actually testing grammar, and for these we use
dnl m4 to generate the test templates.
dnl
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
load interpreter

red in SUBST : insert('var1, bool(true), noSubst) .
red in SUBST : insert('var2, bool(false), insert('var1, bool(true), noSubst)) .
red in SUBST : insert('var2, bool(false), insert('var1, bool(true), noSubst)) ['var1] .
red in SUBST : upTerm(insert('var1, bool(false), noSubst)) .
red in SUBST : downTerm(upTerm(insert('var1, bool(false), noSubst)),noSubst) .
red in SUBST : downTerm(upTerm(insert('var2, bool(true), insert('var1, bool(false), noSubst)) ['var1]), null) .
red in SUBST : dom('var1, insert('var2, bool(true), insert('var1, bool(false), noSubst))) .

GRAMMAR_TEST(GUARDS, wait, noGuard)
GRAMMAR_TEST(GUARDS, bool(true), noGuard)
GRAMMAR_TEST(GUARDS, int(4) & int(5), noGuard)
GRAMMAR_TEST(GUARDS, int(4) & int(5) & wait, noGuard)
GRAMMAR_TEST(GUARDS, 'test ?, noGuard)
GRAMMAR_TEST(GUARDS, 'test ? & 'pest, noGuard)
GRAMMAR_TEST(GUARDS, 'add[[int(4) `#' int(5)]] & 'label ? & wait & bool(true) & wait, noGuard)

GRAMMAR_TEST(STATEMENTS, 'a ::= 'a, skip)
GRAMMAR_TEST(STATEMENTS, skip, 'a ::= 'a)
GRAMMAR_TEST(STATEMENTS, 'var ::= new 'C (int(5) `#' bool(true)), skip)
GRAMMAR_TEST(STATEMENTS, await 'test ? , skip)
GRAMMAR_TEST(STATEMENTS, await (('test ?) & wait), skip)
GRAMMAR_TEST(STATEMENTS, ! 'method (null), skip)
GRAMMAR_TEST(STATEMENTS, 'getNeighbor(null : noAid), skip)
GRAMMAR_TEST(STATEMENTS, 'label ! 'oid . 'mtd (emp), skip)
dnl GRAMMAR_TEST(STATEMENTS, cont (label(5)), skip)
