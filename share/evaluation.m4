dnl Definition of creol statements.
dnl
dnl Copyright (c) 2007, 2008 by Marcel Kyas <kyas@ifi.uio.no>
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
*** Definition of the family of evaluation functions.
***
mod `CREOL-EVAL' is

    protecting CREOL-CONFIGURATION .

    vars L L' : Label .
    vars E E' E'' : Expr .
    vars D D' : Data .
    var DL : DataList .
    var EL : ExprList .
    var NeEL : NeExprList .
    var ES : ExprSet .
    var NeES : NeExprSet .
    var DS : DataSet .
    var EM : ExprMap .
    var A : Vid .
    var AL : VidList .
    vars Q C : String .
    vars S S' : Subst .
    vars ST ST' : Stmt . 
    vars SL SL1 SL2 : StmtList .
    var CN : Configuration .
    var CL : Class .
    var OB : Object .
    var MS : Msg .
    var N : Nat .
    var B : Bool .

    --- Check if a message is in the queue.
    op inqueue  : Label Configuration -> Bool .
    eq inqueue(L, < L' : Future | Completed: B, References: N, Value: DL > CN) =
        if L == L' then B else inqueue(L, CN) fi .
    eq inqueue(L, CL CN) = inqueue(L, CN) .
    eq inqueue(L, OB CN) = inqueue(L, CN) .
    eq inqueue(L, MS CN) = inqueue(L, CN) .
    eq inqueue(L, none) = false .

dnl
dnl Macros for dealing with enabledness and readyness in the timed and
dnl untimed cases.
dnl
ifdef(`WITH_TIME',dnl
    var T : Float .

    op evalGuard : Expr Subst Configuration Float -> Data .
    op evalGuardList : ExprList Subst Configuration Float -> DataList [strat (1 0 0 0 0)] .
    op evalGuardSet : ExprSet Subst Configuration Float -> DataSet [strat (1 0 0 0 0)] .
    op evalGuardMap : ExprMap Subst Configuration Float -> DataMap [strat (1 0 0 0 0)] .
    op enabled : StmtList Subst Configuration Float -> Bool .
    op ready : StmtList Subst Configuration Float -> Bool .
,dnl Untimed:

    op evalGuard : Expr Subst Configuration -> Data .
    op evalGuardList : ExprList Subst Configuration -> DataList [strat (1 0 0 0)] .
    op evalGuardSet : ExprSet Subst Configuration -> DataSet [strat (1 0 0 0)] .
    op evalGuardMap : ExprMap Subst Configuration -> DataMap [strat (1 0 0 0)] .
    op enabled : StmtList Subst Configuration -> Bool .
    op ready : StmtList Subst Configuration -> Bool .
)dnl

    eq EVALGUARD(D, S, CN, T) = D .
    eq EVALGUARD(now, S, CN, T) = ifdef(`WITH_TIME', time(T), time(0.0)) .
    eq EVALGUARD((Q @ C), (S :: S'), CN, T) =  S [Q] .
    eq EVALGUARD(A, S, CN, T) =  S [A] .
    eq EVALGUARD(Q (EL), S, CN, T) = Q ( EVALGUARDLIST(EL, S, CN, T) ) .
    eq EVALGUARD(?(A), S, CN, T) = bool(inqueue(S[A], CN)) .
    eq EVALGUARD(?(L), S, CN, T) = bool(inqueue(L, CN)) .
    eq EVALGUARD(list(EL), S, CN, T) = list(EVALGUARDLIST(EL, S, CN, T)) .
    eq EVALGUARD(set(ES), S, CN, T) = set(EVALGUARDSET(ES, S, CN, T)) .
    eq EVALGUARD(map(EM), S, CN, T) = map(EVALGUARDMAP(EM, S, CN, T)) .
    eq EVALGUARD(if E th E' el E'' fi, S, CN, T) =
      if EVALGUARD(E, S, CN, T) asBool
      then EVALGUARD(E', S, CN, T)
      else EVALGUARD(E'', S, CN, T) fi .

    --- Evaluate guard lists.  This is almost the same as evalList, but we
    --- had to adapt this to guards.
    eq EVALGUARDLIST(emp, S, CN, T) = emp .
    eq EVALGUARDLIST(DL, S, CN, T) = DL .   --- No need to evaluate.
    eq EVALGUARDLIST(E, S, CN, T) = EVALGUARD(E, S, CN, T) .
    eq EVALGUARDLIST(E :: NeEL, S, CN, T) =
      EVALGUARD(E, S, CN, T) :: EVALGUARDLIST(NeEL, S, CN, T) .

    --- Evaluate a set.
    eq EVALGUARDSET(emptyset, S, CN, T) = emptyset .
    eq EVALGUARDSET(DS, S, CN, T) = DS .  ---  No need to evaluate
    eq EVALGUARDSET(E, S, CN, T) = EVALGUARD(E, S, CN, T) .
    eq EVALGUARDSET(E : NeES, S, CN, T) =
    EVALGUARD(E, S, CN, T) : EVALGUARDSET(NeES, S, CN, T) .

    --- Evaluate a map.
    eq EVALGUARDMAP(empty, S, CN, T) = empty .
   eq EVALGUARDMAP((mapentry(D, D'), EM), S, CN, T) =
     (mapentry(D, D') , EVALGUARDMAP(EM, S, CN, T)) .  --- No need to evaluate .
   eq EVALGUARDMAP((mapentry(D, E'), EM), S, CN, T) =
     (mapentry(D, EVALGUARD(E', S, CN, T)) , EVALGUARDMAP(EM, S, CN, T)) .
   eq EVALGUARDMAP((mapentry(E, D'), EM), S, CN, T) =
     (mapentry(EVALGUARD(E, S, CN, T), D') , EVALGUARDMAP(EM, S, CN, T)) .
   eq EVALGUARDMAP((mapentry(E, E'), EM), S, CN, T) =
     (mapentry(EVALGUARD(E, S, CN, T), EVALGUARD(E', S, CN, T)) ,
     EVALGUARDMAP(EM, S, CN, T)) .

    --- Enabledness
    eq ENABLED(await E ; SL, S, CN, T) = EVALGUARD(E, S, CN, T) asBool .
ifdef(`LOGGING',dnl
    eq ENABLED($bawait E ; SL, S, CN, T) = EVALGUARD(E, S, CN, T) asBool .
)dnl
dnl ifdef(`WITH_TIME',dnl
dnl  eq ENABLED(posit E ; SL, S, CN, T) = EVALGUARD(E, S, CN, T) asBool .
dnl)dnl
    eq ENABLED((SL1 [] SL2) ; SL,  S, CN, T) =
         ENABLED(SL1, S, CN, T) or ENABLED(SL2, S, CN, T) .
ifdef(`WITH_MERGE',
`    eq ENABLED((SL1 ||| SL2) ; SL, S, CN, T) =
         ENABLED(SL1, S, CN, T) or ENABLED(SL2, S, CN, T) .
    eq ENABLED((SL1 MERGER SL2) ; SL, S, CN, T) = ENABLED(SL1, S, CN, T) .')
    eq ENABLED(SL, S, CN, T) = true [owise] .

    --- The ready predicate holds, if a statement is ready for execution,
    --- i.e., the corresponding process may be waken up.
    eq READY(get(A ; AL) ; SL , S, CN, T) = inqueue(S[A], CN) . 
    eq READY(get(L ; AL) ; SL , S, CN, T) = inqueue(L, CN) . 
    eq READY((SL1 [] SL2) ; SL, S, CN, T) =
          READY(SL1, S, CN, T) or READY(SL2, S, CN, T) .
ifdef(`WITH_MERGE',
`    eq READY((SL1 ||| SL2) ; SL, S, CN, T) =
	  READY(SL1, S, CN, T) or READY(SL2, S, CN, T) .
    eq READY((SL1 MERGER SL2) ; SL, S, CN, T) = READY(SL1, S, CN, T) .')
    eq READY(SL, S, CN, T) = ENABLED(SL, S, CN, T) [owise] .

endm
