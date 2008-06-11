include(macros.m4)dnl
dnl The usual header.
***
*** Reimplementation of the CREOL KIND, 2007, 2008
***
*** Copyright (c) 2007, 2008
***
*** Do NOT edit this file.  This file may be overwritten.  It has been
*** automatically generated from interpreter.m4 using m4.
***
*** This file has been generated from interpreter.m4 ($Revision$)
***
*** This program is free software; you can redistribute it and/or
*** modify it under the terms of the GNU General Public License as
*** published by the Free Software Foundation; either version 3 of the
*** License, or (at your option) any later version.
***
*** This program is distributed in the hope that it will be useful, but
*** WITHOUT ANY WARRANTY; without even the implied warranty of
*** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
*** General Public License for more details.
***
*** You should have received a copy of the GNU General Public License
*** along with this program.  If not, see <http://www.gnu.org/licenses/>.
***

ifdef(`MODELCHECK', `load model-checker .
')dnl
load creol-datatypes .


***************************************************************************
***
*** Signature of programs and states.
***
***************************************************************************

***
*** Binding variables to values.
***
ifdef(`FAILED-EXPERIMENTS',dnl
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
,dnl
*** Use MAP from prelude.  This seems to be the fastest solution.
***
fmod CREOL-SUBST is
  protecting CREOL-DATATYPES .
  extending MAP{Vid`,' Data} * (sort Map{Vid`,'Data} to Subst`,'
                              sort Entry{Vid`,'Data} to Binding`,'
                              op empty : -> Map{Vid`,'Data} to noSubst) .

  vars A A' : Vid .
  vars D D' : Data .
  vars S1 S2  : Subst .

  *** Lazy composition operator for substitutions
  op _::_ : Subst Subst -> Subst .
  eq (S1 :: S2)[A] = if $hasMapping(S2`,' A) then S2[A] else S1[A] fi .

  *** Composition operater for substitutions
  op compose : Subst Subst -> Subst .
  eq compose(S1`,' noSubst) = S1 .
  eq compose(noSubst`,' S2) = S2 .
  eq compose(S1`,' (S2`,' (A |-> D))) = compose(insert(A`,' D`,' S1)`,' S2) .
endfm
)


*** Creol Statements
***
*** The following module defines all elementary statements of Creol.
fmod CREOL-STATEMENT is
  protecting CREOL-DATA-VIDLIST .
  protecting CREOL-EXPRESSION .
  protecting CREOL-SUBST .

  *** SuspStm is a statement which can be suspended.  It includes
  *** await, [] and ||| (the later two defined in CREOL-STM-LIST.
  sorts Mid Stm SuspStm .
  subsort SuspStm < Stm .
  subsort String < Mid .

  op _._ : Expr String -> Mid [ctor prec 33] .
  op _@_ : String String -> Mid [ctor prec 33] .

  op skip : -> Stm [ctor] .
  op release : -> Stm [ctor] .
  op _::=_ : VidList ExprList -> Stm [ctor prec 35] .
  op _::= new_(_) : Vid String ExprList -> Stm [ctor prec 35 `format' (d b d o d d d d)] .
  op _!_(_) : Vid Mid ExprList -> Stm [ctor prec 39] .
  op _?(_)  : Vid VidList -> Stm [ctor prec 39 `format' (d c o d d d)] .
  op _?(_)  : Label VidList -> Stm [ctor ditto] .
  op await_ : Expr -> SuspStm [ctor `format' (! o d)] .
  op posit_ : Expr -> SuspStm [ctor `format' (! o d)] .
  op return : ExprList -> Stm [ctor `format' (c o)] .
  op free : Vid -> Stm [ctor `format' (c o)] .
  op cont : Label -> Stm [ctor `format' (c o)] .
  op tailcall_(_) : Mid ExprList -> Stm [ctor `format' (c o c o c o)] .
  op accept : Label -> Stm [ctor `format' (c o)] .

  --- multiple assignment
  ---
  --- For the model checker the following will be evaluated as an
  --- equation and the old rule is not confluent.

  op assign : VidList DataList -> Stm [ctor `format' (c o)] .

endfm

view Stm from TRIV to CREOL-STATEMENT is
   sort Elt to Stm .
endv



*** Specification of compound statements.
***
fmod CREOL-STM-LIST is
  protecting CREOL-STATEMENT .                
  protecting LIST{Stm} * (sort List{Stm} to StmList,
                          sort NeList{Stm} to NeStmList,
			  op nil : -> List{Stm} to noStm,
			  op __ : List{Stm} List{Stm} -> List{Stm} to _;_ [`format' (d r o d)]) .

  op if_th_el_fi : Expr NeStmList NeStmList -> Stm [ctor] . 
  op while_do_od : Expr NeStmList -> Stm [ctor] .
  op _[]_  : NeStmList NeStmList -> SuspStm [ctor comm assoc prec 45 `format' (d r d o d)] .
  op _|||_ : NeStmList NeStmList -> SuspStm [ctor comm assoc prec 47 `format' (d r o d)] .
  op _MERGER_  : StmList StmList -> Stm [ctor assoc] .

  var SL : StmList .
  var NeSL : NeStmList .
  var AL : VidList .
  var DL : DataList .
  var EL : ExprList .
  var B : Expr .

  *** Some simplifications:
  eq noStm MERGER SL = SL .
  eq SL MERGER noStm = SL .

  --- Optimize assignments.  This way we save reducing a skip.  Also note
  --- that the empty assignment is /not/ programmer syntax, it is inserted
  --- during run-time.
  eq (noVid ::= emp) = noStm .
  eq assign(noVid, emp) = noStm .

endfm

fmod CREOL-PROCESS is

  protecting CREOL-STM-LIST .

  sort Process .

  op idle : -> Process [ctor `format' (!b o)] .  
  op notFound : -> Process [ctor `format' (!b o)] .  
  op _,_ : Subst StmList -> Process [ctor `format' (o r sbu o)] . 

  var L : Subst .
  eq (L, noStm) = idle . --- if ".label" is needed this is dangerous!
  eq idle = (noSubst, noStm) [nonexec metadata "Will cause infinite loops."] .

endfm



*** Specifies a process pool, here a multiset of Processes
***
fmod CREOL-PROCESS-POOL is

  protecting CREOL-PROCESS .

  sort MProc .
  subsort Process < MProc .
  op noProc : -> MProc [ctor] .
  op _++_ : MProc MProc -> MProc
    [ctor assoc comm id: noProc prec 41 `format' (d r os d)] .

endfm



*** An inherits declaration
***
fmod CREOL-INHERIT is
  protecting CREOL-DATATYPES .
  sort Inh .

  op  _<_> : String  ExprList -> Inh [ctor prec 15] .

endfm

view Inh from TRIV to CREOL-INHERIT is
  sort Elt to Inh .
endv

fmod CREOL-METHOD is
  protecting CREOL-STM-LIST .
  sort Method .

  op <_: Mtdname | Param:_, Latt:_, Code:_> : 
    String VidList Subst StmList -> Method [ctor
      `format' (b d o d d sb o d sb o d sb o b o)] .

endfm

view Method from TRIV to CREOL-METHOD is
  sort Elt to Method .
endv


*** Define object identifiers.
***
fmod CREOL-DATA-OID is
  extending CREOL-DATA-SIG .
  protecting CONVERSION .
  protecting STRING .
  protecting NAT .

  sort Oid .
  subsort Oid < Data .

  op ob : String -> Oid [ctor] .

  var C : String .
  var N : Nat .

  --- Create a new fresh name for an object.
  op newId : String Nat -> Oid .
  eq newId(C, N)  = ob(C + string(N,10)) .

endfm

view Oid from TRIV to CREOL-DATA-OID is
  sort Elt to Oid .
endv




***
*** CREOL Classes
***
changequote(`[[[[', `]]]]')dnl
fmod CREOL-CLASS is
  protecting LIST{Inh} * (sort List{Inh} to InhList,
			  sort NeList{Inh} to NeInhList,
			  op nil : -> List{Inh} to noInh,
			  op __ : List{Inh} List{Inh} -> List{Inh} to _`,`,_) .
  protecting SET{Method} * (sort Set{Method} to MMtd,
			    op empty : -> Set{Method} to noMethod,
                            op _`,_ : Set{Method} Set{Method} -> Set{Method} to _*_ [[[[[format]]]] (d d ni d)] ) .
changequote dnl
  protecting CREOL-PROCESS .

  --- Class declaration.
  ---
  sort Class .
  op <_: Cl | Inh:_, Par:_, Att:_, Mtds:_, Ocnt:_> : 
    String InhList VidList Subst MMtd Nat -> Class 
     [ctor `format' (ng d o d d  sg o d  sg o d  sg o d  sg++ oni o  gni o-- g o)] .

endfm


***
*** CREOL messages and queues
***
fmod CREOL-MESSAGE is
  protecting CREOL-DATA-OID .
  protecting CREOL-DATA-LABEL .

  sort Body Invoc Comp .
  subsorts Invoc Comp < Body .

  *** INVOCATION and REPLY
  op invoc : Oid Label String DataList -> Invoc [ctor `format'(b o)] .  
  op comp : Label DataList -> Comp [ctor `format' (b o)] .  

  --- Messages.  Messages have at least a receiver.

  sort Message .

  --- Invocation and completion message.
  op _from_to_ : Body Oid Oid -> Message [ctor `format' (o ! o ! o on)] .

  --- Error and warning messages are intended to stop the machine.
  --- For now, nothing is emitting these.
  --- op error(_) : String -> [Message] [ctor `format' (nnr r o! or onn)] .
  op warning(_) : String -> [Message] [ctor `format' (nnr! r! r! or onn)] .

endfm

view Message from TRIV to CREOL-MESSAGE is
   sort Elt to Message .
endv

view Body from TRIV to CREOL-MESSAGE is
   sort Elt to Body .
endv

--- A multiset of messages.
fmod CREOL-MESSAGES is
  protecting CREOL-MESSAGE .

  sort MMsg .
  subsort Body < MMsg .

  op noMsg : -> MMsg [ctor] .
  op _+_ : MMsg MMsg -> MMsg [ctor assoc comm id: noMsg] . 

endfm

fmod CREOL-LABELS is

  protecting CREOL-DATA-LABEL .

  sort Labels .
  subsort Label < Labels .

  op noDealloc : -> Labels [ctor] .
  op _^_ : Labels Labels -> Labels [ctor comm assoc id: noDealloc] .

endfm



***
*** CREOL objects
***
fmod CREOL-OBJECT is
  protecting CREOL-MESSAGES .
  protecting CREOL-LABELS .
  protecting CREOL-PROCESS-POOL .

  sort Object .

  op noObj : -> Object [ctor] .
  op <_:_ | Att:_, Pr:_, PrQ:_, Dealloc:_, Ev:_, Lcnt:_> : 
       Oid String Subst Process MProc Labels MMsg Nat -> Object 
         [ctor `format' (nr d d g ++r nir o  r ni o  r ni o  r ni o  r ni o  r ni o--  r o)] .

endfm


fmod `CREOL-EVAL' is

  protecting CREOL-DATA-SIG .
  protecting CREOL-SUBST .
  protecting CREOL-STM-LIST .
  protecting CREOL-MESSAGES .

  vars N N' : Nat .
  vars L L' : Label .
  vars E E' E'' : Expr .
  vars D D' : Data .
  var EL : ExprList .
  var NeEL : NeExprList .
  var DL : DataList .
  var ES : ExprSet .
  var NeES : NeExprSet .
  var DS : DataSet .
  var NeDS : NeDataSet .
  var A : Vid .
  var Q : String .
  var S S' : Subst .
  var MM : MMsg .
  var C : String .

  *** Check if a message is in the queue.
  op inqueue  : Label MMsg -> Bool .
  eq inqueue(L, noMsg) = false .
  eq inqueue(L, MM + comp(L', EL)) =
	if L == L' then true else inqueue(L, MM) fi .

  vars ST ST' : Stm . 
  vars SL SL1 SL2 : StmList . 
  vars NeSL NeSL1 NeSL2 : NeStmList .
  var AL : VidList .
  var M : ExprMap .
dnl
dnl Macros for dealing with enabledness and readyness in the timed and
dnl untimed cases.
dnl
ifdef(`TIME',dnl
  var T : Float .

  op evalGuard : Expr Subst MMsg Float -> Data .
  op evalGuardList : ExprList Subst MMsg Float -> DataList [strat (1 0 0 0 0)] .
  op evalGuardSet : ExprSet Subst MMsg Float -> DataSet [strat (1 0 0 0 0)] .
  op evalGuardMap : ExprMap Subst MMsg Float -> DataMap [strat (1 0 0 0 0)] .
  op enabled : NeStmList Subst MMsg Float -> Bool .
  op ready : NeStmList Subst MMsg Float -> Bool .
,dnl Untimed:

  op evalGuard : Expr Subst MMsg -> Data .
  op evalGuardList : ExprList Subst MMsg -> DataList [strat (1 0 0 0)] .
  op evalGuardSet : ExprSet Subst MMsg -> DataSet [strat (1 0 0 0)] .
  op evalGuardMap : ExprMap Subst MMsg -> DataMap [strat (1 0 0 0)] .
  op enabled : NeStmList Subst MMsg -> Bool .
  op ready : NeStmList Subst MMsg -> Bool .
)dnl

  eq EVALGUARD(D, S, MM, T) = D .
  eq EVALGUARD(now, S, MM, T) = ifdef(`TIME', time(T), time(0.0)) .
  eq EVALGUARD((Q @@ C), (S :: S'), MM, T) =  S [Q] .
  eq EVALGUARD(Q, (S :: S'), MM, T) =  S' [Q] [nonexec] . *** XXX: Later
  eq EVALGUARD(A, S, MM, T) =  S [A] .
  eq EVALGUARD(Q (EL), S, MM, T) = Q ( EVALGUARDLIST(EL, S, MM, T) ) .
  eq EVALGUARD((A ??), S, MM, T) = bool(inqueue(S[A], MM)) .
  eq EVALGUARD((L ??), S, MM, T) = bool(inqueue(L, MM)) .
  eq EVALGUARD(list(EL), S, MM, T) = list(EVALGUARDLIST(EL, S, MM, T)) .
  eq EVALGUARD(pair(E,E'),S, MM, T) =
    pair(EVALGUARD(E, S, MM, T), EVALGUARD(E', S, MM, T)) .
  eq EVALGUARD(set(ES), S, MM, T) = set(EVALGUARDSET(ES, S, MM, T)) .
  eq EVALGUARD(map(M), S, MM, T) = map(EVALGUARDMAP(M, S, MM, T)) .
  eq EVALGUARD(if E th E' el E'' fi, S, MM, T) =
    if EVALGUARD(E, S, MM, T) asBool
    then EVALGUARD(E', S, MM, T)
    else EVALGUARD(E'', S, MM, T) fi .

  *** Evaluate guard lists.  This is almost the same as evalList, but we
  *** had to adapt this to guards.
  eq EVALGUARDLIST(emp, S, MM, T) = emp .
  eq EVALGUARDLIST(DL, S, MM, T) = DL .   --- No need to evaluate.
  eq EVALGUARDLIST(E, S, MM, T) = EVALGUARD(E, S, MM, T) .
  eq EVALGUARDLIST(E :: NeEL, S, MM, T) =
    EVALGUARD(E, S, MM, T) :: EVALGUARDLIST(NeEL, S, MM, T) .

  eq EVALGUARDSET(emptyset, S, MM, T) = emptyset .
  eq EVALGUARDSET(DS, S, MM, T) = DS .  ---  No need to evaluate
  eq EVALGUARDSET(E, S, MM, T) = EVALGUARD(E, S, MM, T) .
  eq EVALGUARDSET(E : NeES, S, MM, T) =
    EVALGUARD(E, S, MM, T) : EVALGUARDSET(NeES, S, MM, T) .

  *** Evaluate a map.
  eq EVALGUARDMAP(empty, S, MM, T) = empty .
 eq EVALGUARDMAP((D |~> D', M), S, MM, T) =
   (D |~> D' , EVALGUARDMAP(M, S, MM, T)) .  --- No need to evaluate .
 eq EVALGUARDMAP((D |~> E', M), S, MM, T) =
   (D |~> EVALGUARD(E', S, MM, T) , EVALGUARDMAP(M, S, MM, T)) .
 eq EVALGUARDMAP((E |~> D', M), S, MM, T) =
   (EVALGUARD(E, S, MM, T) |~> D' , EVALGUARDMAP(M, S, MM, T)) .
 eq EVALGUARDMAP((E |~> E', M), S, MM, T) =
   (EVALGUARD(E, S, MM, T) |~> EVALGUARD(E', S, MM, T) ,
   EVALGUARDMAP(M, S, MM, T)) .

  eq ENABLED((NeSL [] NeSL1) ; SL2,  S, MM, T) =
       ENABLED(NeSL, S, MM, T) or ENABLED(NeSL1, S, MM, T) .
  eq ENABLED((NeSL ||| NeSL1) ; SL2, S, MM, T) =
       ENABLED(NeSL, S, MM, T) or ENABLED(NeSL1, S, MM, T) .
  eq ENABLED((NeSL MERGER SL1) ; SL2, S, MM, T) = ENABLED(NeSL, S, MM, T) .
  eq ENABLED(await E ; SL2, S, MM, T) = EVALGUARD(E, S, MM, T) asBool .
dnl ifdef(`TIME',dnl
dnl  eq ENABLED(posit E ; SL2, S, MM, T) = EVALGUARD(E, S, MM, T) asBool .
dnl)dnl
  eq ENABLED(NeSL, S, MM, T) = true [owise] .

  *** The ready predicate holds, if a statement is ready for execution,
  *** i.e., the corresponding process may be waken up.
  eq READY((NeSL [] NeSL1) ; SL2, S, MM, T) =
        READY(NeSL, S, MM, T) or READY(NeSL1, S, MM, T) .
  eq READY((NeSL ||| NeSL1) ; SL2, S, MM, T) =
	READY(NeSL, S, MM, T) or READY(NeSL1, S, MM, T) .
  eq READY((NeSL MERGER SL1) ; SL2, S, MM, T) = READY(NeSL, S, MM, T) .
  eq READY((A ?(AL)) ; SL2 , S, MM, T) = inqueue(S[A], MM) . 
  eq READY((L ?(AL)) ; SL2 , S, MM, T) = inqueue(L, MM) . 
  eq READY(NeSL, S, MM, T) = ENABLED(NeSL, S, MM, T) [owise] .

endfm

*** STATE CONFIGURATION ***
fmod CREOL-CONFIG is
  protecting CREOL-OBJECT .
  protecting CREOL-CLASS .

  sort Configuration .

ifdef(`TIME', `  sort Clock .')

  subsorts Class ifdef(`TIME', `Clock ')Message Object < Configuration .

  op noConf : -> Configuration [ctor] .
  op __ : Configuration Configuration -> Configuration
	[ctor assoc comm id: noConf `format' (d n d)] .

ifdef(`TIME',dnl
  *** Definition of a global clock in the system
  op < _: Clock | delta: _> : Float Float -> Clock
    [ctor ``format'' (c o c c c c o c o)] .
)dnl

  *** Useful for real-time maude and some other tricks.
ifdef(`MODELCHECK',dnl
  *** Maude's model checker asks us to provide State.
  including SATISFACTION .
  including MODEL-CHECKER .

  op {_} : Configuration -> State [ctor] .
,dnl
  *** We should not provide sort State`,' since this is used in LOOP-MODE.
)dnl

  *** System initialisation
  var C : String .
  var DL : DataList .
  op main : String DataList -> Configuration .
  eq main(C,DL) =
    < ob("main") : "" | Att: noSubst, 
      Pr: ("var" |-> null, ("var" ::= new C(DL))), PrQ: noProc,
      Dealloc: noDealloc, Ev: noMsg, Lcnt: 0 > .

endfm

include(`machine.m4')

ifdef(`MODELCHECK', include(`predicates.m4'))dnl

eof
