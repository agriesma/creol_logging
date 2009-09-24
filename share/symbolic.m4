dnl A simple term replacement system for Creol.
dnl
dnl Copyright (c) 2009 by Andreas Griesmayer <gismo@kangaroo.at>
dnl   and Marcel Kyas <kyas@ifi.uio.no>
dnl
dnl Do NOT edit this file.  This file may be overwritten.  It has been
dnl automatically generated from interpreter.m4 using m4.
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
mod `CREOL-SYMBOLIC' is

    protecting CREOL-REPLACE .

------------------------------------------------------------------------
--- compute and work with symbolic transition relations
------------------------------------------------------------------------
--- a transition relation shows how the variables change by execution
--- of a statement.  The transitionrelation is stored in a map similar
--- to an assignment statement - a form that makes backward reasoning
--- easy.  The key is the next state variable`,' the value an expression
--- that describes the state change in therm of the current
--- variables. e.g. for two variables in the writing of parallel
--- assignments: 
--- x'`,' y' = f(x, y)`,' g(x,y) ; 
--- x"`,' y" = f'(x', y')`,' g'(x', y') 
--- this sequence of statements can be combined by replacing x' and y'
---  - the "middle" variables - by the expressions f and g to
--- x"`,' y" = f'(f(x, y), g(x, y))`,' g'(f(x, y), g(x, y))
---
--- initial states that fulfill a condition c(x", y") can easily be
--- computed by replacing x" and y" by their respective expressions in
--- terms of x and y
---
------------------------------------------------------------------------
--- give variables a unique name
--- --------------------------------------------------------------------
--- The log is a serialized version of Creol.  Statements from
--- different methods and objects are interleaved and might operate on
--- variables that are actually different`,' but have the same name.  To
--- avoid the necessity to consider the scope at the execution of
--- every statement`,' the variables are renamed to a unique name`,' by
--- prefixing them with an identifyer.  The object ID is used for
--- global variables`,' and the label for local variables.


------------
--- Declarations
------------

    vars TS1 TS2 TS3 : TSubst .
    var V1 : Vid .
    var S L : Subst .
    var C CC Q : String . 
    vars E1 E2 : Expr .
    var F : Nat .
    var O : Oid .
    var AL : VidList .
    var EL : ExprList .
    var transstmt : Stmt .

--- generate Transitions with unique variable names
    op getTrans : Stmt -> TSubst .
    op getTrans : Stmt Subst Subst -> TSubst .
    op getTrans : Stmt TSubst TSubst -> TSubst .
    op getTrans : Stmt TSubst -> TSubst .
    op renStmt : Stmt Subst Subst -> Stmt .
    op renStmt : Stmt TSubst -> Stmt .
    op renExpr : Subst Subst Expr -> Expr .
    op replacementMap : Subst Subst -> TSubst .
    op replacementMap : Subst String TSubst -> TSubst .

--- append and merge transitions
    op appendTrans : TSubst TSubst -> TSubst .
    op replaceMiddle : TSubst TSubst -> TSubst .
    op replaceMiddle : TSubst TSubst TSubst -> TSubst .  
    op mergeTrans : TSubst TSubst -> TSubst .

--- helper functions
    op label : Oid Nat -> Label [ctor ``format'' (o o)] .
    op toString : Label -> String .
    op toString : Oid -> String .
    op getThis : Subst -> String .
    op getLabel : Subst -> String .
    op size : TSubst -> Nat .
    op size : TSubst Nat -> Nat .
    op delete : Vid TSubst -> TSubst .
    op toTrans : Subst -> TSubst .
    op getParams : TSubst -> ExprList .
    op insertPassing : Vid ExprList TSubst -> TSubst .
    op unpack : Expr -> ExprList .

------------
--- Equations
------------
    eq unpack(list(EL)) = EL .
    eq getTrans( transstmt) = getTrans(transstmt, noSubst, noSubst) .
    eq getTrans( transstmt, S, L) = getTrans (transstmt, replacementMap(S, L), TnoSubst ) .
    eq getTrans( assign( AL ; EL ) , TS1, TS2)
     = getTrans( assign( replace(removeAt(AL) , TS1) ; replace(EL, TS1) ), TS2) . 
    eq getTrans( assign((V1, AL) ; (E1 :: EL)), TS2) = getTrans( assign(AL ; EL), insert(V1, E1, TS2) ) .
    eq getTrans( call(C ; E1 ; Q ; EL ), TS1, TS2) = getTrans( call(C ; E1 ; Q ; replace(EL, TS1) ), TS2 ) .
    eq getTrans( call(C ; E1 ; Q ; EL ), TS2)
     = "params" |> list(EL) .
    eq getTrans( new(C ; CC ; EL ), TS1, TS2 ) = getTrans( new(C ; CC ; replace(EL, TS1) ), TS2 ) .
    eq getTrans( new(C ; CC ; (EL) ), TS2) 
     = "params" |> list(EL) .
    eq getTrans( return( EL ), TS1, TS2 ) = getTrans( return(replace(EL, TS1)), TS2 ) .
    eq getTrans( return(EL), TS2 ) 
     = "params" |> list(EL) .
    eq getTrans( noStmt, TS2) = TS2 .

    eq renExpr(S, L, EL) = replace(EL, replacementMap(S, L) ) .
    eq renStmt( transstmt, S, L) = renStmt( transstmt, replacementMap(S, L) ) .
    eq renStmt( assign( AL ; EL), TS1) = assign(replace(AL, TS1); replace(EL, TS1) ) .

    eq replacementMap(S, L) = replacementMap(L, getLabel((L, S)), replacementMap(S, getThis((L, S)), TnoSubst) ) .
    eq replacementMap((  V1 |-> E1 , S ), Q, TS1) = replacementMap(S, Q, insert(V1, (Q + "." + V1), TS1) ) .
    eq replacementMap( noSubst, Q, TS1) = TS1 .


--- appendTrans(TS1, TS2) : append TS2 to TS1 by replacing the
--- variables in TS2 by the expressions given in TS1.  Variables that
--- are not redefined in TS2 are taken from TS1.
    eq appendTrans ( TS1, TS2 ) = mergeTrans(TS1, replaceMiddle( TS2, TS1 ) ) .

    op filter : TSubst -> TSubst .
    op filter : TSubst TSubst -> TSubst .
    eq filter( TS1) = filter(TS1, TnoSubst) .
    eq filter( ( V1 |> E1, TS1 ) , TS2 ) = 
       if ``substr(V1, sd(length(V1),5), 5)'' =/= "_init" then
         filter(TS1, insert(V1, E1, TS2) )
       else
         filter(TS1, TS2)
       fi .
    eq filter(TnoSubst, TS2) = TS2 .



--- filters all variables starting with C (exept _init variables).  Is used to 
--- remove the local variables when they are not needed anymore (after an return)
    op filterprefix : TSubst String -> TSubst .
    op filterprefix : TSubst TSubst String -> TSubst .

    eq filterprefix(TS1, C ) = filterprefix(TS1, TnoSubst, C ) .
    eq filterprefix(TnoSubst, TS2, C ) = TS2 . 
    eq filterprefix( (V1 |> E1, TS1), TS2, C ) =
       if ``substr(V1, 0, length(C))'' == C then
         if ``substr(V1, sd(length(V1),5), 5)'' == "_init" then
           filterprefix(TS1, insert( V1, E1, TS2), C)
         else
          filterprefix(TS1, TS2, C)
         fi 
       else
          filterprefix(TS1, insert( V1, E1, TS2), C)
       fi .

--- replaces the variables in the expressions of TS1 with their values in TS2
--- e.g. if "x" |> "y" in TS1 and "y" |> int(5) in TS2`,' the result is "x" |> int(5)
    eq replaceMiddle( TS1, TS2 ) = replaceMiddle( TS1, filter(TS2), TnoSubst) .
    eq replaceMiddle( TnoSubst, TS2, TS3 ) = TS3 .
    eq replaceMiddle( (V1 |> E1, TS1), TS2, TS3 ) = replaceMiddle( TS1, TS2, insert( V1, replace (E1, TS2), TS3) ) .
    

--- insertTrans(T1, T2): insert all variables from T2 into T1`,' overwriting values in T1
    eq mergeTrans( TS1, TnoSubst ) = TS1 .
    eq mergeTrans( TS1, (V1 |> E1, TS2)) = mergeTrans( insert (V1, E1, TS1), TS2 ) .

    eq  toString(label(ob(Q), F) ) = Q + "-" + string(F, 10) .
    eq  toString(ob(Q) ) = Q .
    ceq getThis(S) = toString(S["this"]) if $hasMapping(S, "this") .
    eq  getThis(S) = "global" [owise] .
    ceq getLabel(S) = toString(S[".label"]) if $hasMapping(S, ".label") .
---    ceq getLabel(S) = toString(S["this"]) if $hasMapping(S, "this") .
    eq  getLabel(S) = "nolabel" [owise] .

    eq size(TS1) = size (TS1, 0) .
    eq size(TnoSubst, F ) = F .
    eq size((TS1, V1 |> E2), F) = size(TS1, F + 1) .

---  delete the key C from a map (must exist! - deadlock otherwise)
    eq delete(C , (TS1, C |> E1)) = TS1 .

--- convert a Subst to TSubst
    eq toTrans(noSubst) = TnoSubst .
    eq toTrans( ( V1 |-> E1, S) ) = insert( V1, E1, toTrans(S) ) .

    op toTrans : ExprList -> TSubst .
    eq toTrans(emp) = TnoSubst . 
    eq toTrans(EL) = "el" |> list(EL) .

--- get the parameters from an transition map
    eq getParams( TS1 ) = unpack(TS1["params"]) .

--- insertPassing: insert params to pass to called methods or new
--- instances.  if the list of params is empty`,' the call is ignored
    eq insertPassing( V1 , emp , TS1 ) = TS1 .
    eq insertPassing( V1 , E1 :: EL , TS1 ) = insert(V1, list(E1 :: EL), TS1) .

endm
