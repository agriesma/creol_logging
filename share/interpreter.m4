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

  var Ih : Inh . 
  var IL : InhList .
  var S : Subst . 
  var SL : StmList . 
  var MM : MMtd .
  var DL : DataList .
  var EL : ExprList .
  var Lab : Label .
  var O : Oid .
  var N : Nat .
  var AL : VidList .
  vars M M' C : String .

  --- Class declaration.
  ---
  sort Class .
  op <_: Cl | Inh:_, Par:_, Att:_, Mtds:_, Ocnt:_> : 
    String InhList VidList Subst MMtd Nat -> Class 
     [ctor `format' (ng d o d d  sg o d  sg o d  sg o d  sg++ oni o  gni o-- g o)] .

  --- fetches pair (code, vars) to bind call to process.
  --- M represents the name of the method.
  --- C represents the name of the class.
  --- MM represents the methods we search through.
  --- O represents the identity of the caller.
  --- Lab represents the label used to return the value computed by the method.
  --- DL represents the list of actual arguments.
  op get : String String MMtd Oid Label DataList -> Process .
  eq get(M, C, MM *
               < M' : Mtdname | Param: AL, Latt: S, Code: SL >, O, Lab, DL) =
    if M == M' then
      ((S, "caller" |-> O, ".class" |-> str(C), ".label" |-> Lab,
        ".method" |-> str(M)),
       assign(AL, DL) ; SL)
    else
      get(M, C, MM, O, Lab, DL)
    fi .

  eq get(M, C, noMethod, O, Lab, DL) = notFound .

endfm


***
*** CREOL messages and queues
***
fmod CREOL-MESSAGE is
  protecting CREOL-CLASS .

  sort Body Invoc Comp .
  subsorts Invoc Comp < Body .

  *** INVOCATION and REPLY
  op invoc : Oid Label String DataList -> Invoc [ctor `format'(b o)] .  
  op comp : Label DataList -> Comp [ctor `format' (b o)] .  

  --- Messages.  Messages have at least a receiver.

  sort Msg .

  --- Invocation and completion message.
  op _from_to_ : Body Oid Oid -> Msg [ctor `format' (o ! o ! o on)] .

  --- Method binding messages.
  --- Bind method request
  --- Given: caller callee label method params (list of classes to look in)
  op bindMtd : Oid Oid Label String DataList InhList -> Msg [ctor `format'(!r d)] .

  --- Successfully bound method body. 
  --- Consider the call O.Q(I). bindMtd(O,Q,I,C S) tries to find Q in
  --- class C or superclasses, then in S. boundMtd(O,Mt) is the result.
  op boundMtd : Oid Process -> Msg [ctor `format'(!r d)] .

  --- Error and warning messages are intended to stop the machine.
  --- For now, nothing is emitting these.
  --- op error(_) : String -> [Msg] [ctor `format' (nnr r o! or onn)] .
  op warning(_) : String -> [Msg] [ctor `format' (nnr! r! r! or onn)] .

endfm

view Msg from TRIV to CREOL-MESSAGE is
   sort Elt to Msg .
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


*** STATE CONFIGURATION ***
fmod CREOL-CONFIG is
  protecting CREOL-OBJECT .

  sort Configuration .
ifdef(`TIME', `  sort Clock .')

  subsorts Class ifdef(`TIME', `Clock ')Msg Object < Configuration .

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

fmod `CREOL-EVAL' is

  protecting CREOL-DATA-SIG .
  protecting CREOL-SUBST .
  protecting CREOL-CONFIG .
  protecting CONVERSION .

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

*** THE MACHINE ***
mod CREOL-SIMULATOR is

  protecting CREOL-DATA-SIG .
  protecting `CREOL-EVAL' .

  op simurev : -> String .
  eq simurev = "KIND $Revision$" .

  vars O O' : Oid .                    --- Object identifiers
  vars C CC : String .                 --- Class names
  vars A A' : Vid .                    --- Generic attribute names
  vars Q Q' : String .                 --- Generic names (attribute and method)
  var AL : VidList .                   --- List of LHS
  var D : Data .                       --- Value
  var DL : DataList .                  --- List of values
  vars E E' G : Expr .                 --- Expressions E, E' and Guard G
  vars EL EL' : ExprList .             --- List of Expressions
  var ST : Stm .                       --- Statement
  var SuS : SuspStm .                  --- Suspendable statement
  vars SL SL1 SL2 : StmList .          --- List of statements
  vars NeSL NeSL1 : NeStmList .
  vars P P' : Process .
  var W : MProc .
  vars S S' L L' : Subst .
  vars N F : Nat .
  vars I I' : InhList .
  var MS : MMtd .
  vars Lab Lab' : Label .
  var LS : Labels .
  var MM : MMsg .
  var cmsg : Comp .
ifdef(`TIME',dnl
  var cnf : Configuration .            --- Configuration
)dnl

dnl Define the clock and the variables needed to address clocks.
dnl
dnl If TIME is not defined, CLOCK will be defined to empty.
ifdef(`TIME',
  vars delta T : Float .
`define(`CLOCK', `< T : Clock | delta: delta >')',dnl
`define(`CLOCK', `')')dnl

ifdef(`MODELCHECK',dnl
  op label : Oid Oid String DataList -> Label [ctor ``format'' (! o)] .
  eq caller(label(O, O', Q, DL)) = O . 
,dnl
 op label : Oid Nat -> Label [ctor ``format'' (o o)] .
 eq caller(label(O, N)) = O .
)dnl


--- assignment
---
--- Execute an assignment.  First, all expressions on the left hand side
--- of the assignment are evaluated and the statement is rewritten to
--- an assign form.
STEP(dnl
`< O : C | Att: S, Pr: (L, AL ::= EL ; SL),
	    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`< O : C | Att: S, Pr: (L,(assign(AL, EVALLIST(EL, (S :: L), T)) ; SL)), 
	    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`[label assignment]')

eq
  < O : C | Att: S, Pr: (L, ( assign(((Q @@ CC), AL), D :: DL) ; SL)),
    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
    < O : C | Att: insert(Q, D, S), Pr: (L, assign(AL, DL) ; SL), PrQ: W,
      Dealloc: LS, Ev: MM, Lcnt: N > 
  [label do-static-assign] .

eq
  < O : C | Att: S, Pr: (L,( assign( (Q, AL), D :: DL) ; SL)), PrQ: W,
    Dealloc: LS, Ev: MM, Lcnt: N >
  =
  if $hasMapping(L, Q) then
    < O : C | Att: S, Pr: (insert(Q, D, L), assign(AL, DL) ; SL), PrQ: W,
      Dealloc: LS, Ev: MM, Lcnt: N > 
  else
    < O : C | Att: insert(Q, D, S), Pr: (L, assign(AL, DL) ; SL), PrQ: W,
      Dealloc: LS, Ev: MM, Lcnt: N >
  fi
  [label do-assign] .



--- Skip
---
STEP(dnl
`< O : C | Att: S, Pr: (L, skip ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`< O : C | Att: S, Pr: (L, SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`[label skip]')


--- if_then_else
---
STEP(dnl
< O : C | Att: S`,' Pr: (L`,' if E th SL1 el SL2 fi ; SL)`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  CLOCK,
if EVAL(E, (S :: L), T) asBool then
    < O : C | Att: S`,' Pr: (L`,' SL1 ; SL)`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  else
    < O : C | Att: S`,' Pr: (L`,' SL2 ; SL)`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  fi
  CLOCK,
`[label if-then-else]')


--- while
---
--- During model checking we want to be able to observe infinite loops.
--- Therefore, it is always a rule.
---
rl
  < O : C | Att: S, Pr: (L, while E do SL od ; SL1), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =>
  < O : C | Att: S,
            Pr: (L, (if E th (SL ; while E do SL od) el skip fi); SL1),
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  [label while] .


--- Non-deterministic choice
---
--- Choice is comm, so [choice] considers both NeSL and NeSL1.
---
crl
  < O : C | Att: S, Pr: (L, (NeSL [] NeSL1); SL), PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: (L, (NeSL ; SL)), PrQ: W, Dealloc: LS, Ev: MM,
            Lcnt: N > CLOCK
  if READY(NeSL, (S :: L), MM, T)
  [label choice] .


--- Merge
---
--- Merge is comm, so [merge] considers both NeSL and NeSL1.
---
crl
  < O : C | Att: S, Pr: (L, (NeSL ||| NeSL1); SL), PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: (L, (NeSL MERGER NeSL1); SL), PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: N > CLOCK
  if READY(NeSL,(S :: L), MM, T)
  [label merge] .

--- merger
---
eq
  < O : C | Att: S,  Pr:  (L, ((ST ; SL1) MERGER NeSL1); SL), PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =
  if ENABLED(ST, (S :: L), MM, T) then
    < O : C | Att: S, Pr: (L, ((ST ; (SL1 MERGER NeSL1)); SL)), PrQ: W,
      Dealloc: LS, Ev: MM, Lcnt: N >
  else
    < O : C | Att: S, Pr: (L, ((ST ; SL1) ||| NeSL1); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >   
  fi CLOCK
 [label merger] .


--- PROCESS SUSPENSION

--- release
---
--- The release statement is an unconditional processor release point.
---
STEP(dnl
`< O : C | Att: S, Pr: (L, release ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`< O : C | Att: S, Pr: idle, PrQ: W ++ (L, SL), Dealloc: LS, Ev: MM, Lcnt: N >',
`[label release]')


--- suspend
---
CSTEP(dnl
`< O : C | Att: S, Pr: (L, SuS ; SL), PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
`< O : C | Att: S, Pr: idle, PrQ: W ++ (L, SuS ; SL), Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
not ENABLED(SuS, (S :: L), MM, T),
`[label suspend]')


--- await
---
CSTEP(dnl
`< O : C | Att: S, Pr: (L, await G ; SL), PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
`< O : C | Att: S, Pr: (L,SL) , PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
`EVALGUARD(G, (S :: L), MM, T) asBool'
`[label await]')

--- Optimze label access in await statements.
eq
  < O : C | Att: S, Pr: (L, await (A ??) ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  < O : C | Att: S, Pr: (L, await ((L[A]) ??) ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  .


--- Schedule a new process for execution, if it is ready.
---
--- Must be a rule to preserve confluence.
---
crl
  < O : C | Att: S, Pr: idle, PrQ: W ++ (L, SL), Dealloc: LS, Ev: MM,
            Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: (L, SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  if READY(SL, (S :: L), MM, T)
  [label PrQ-ready] .


--- METHOD CALLS
---

--- OPTIMISATION: Reduce the value of a label in a process to avoid
--- constant re-evaluation
eq < O : C | Att: S, Pr: (L, A ?(AL); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > =
  < O : C | Att: S, Pr: (L, (L[A])?(AL); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > .


dnl receive-invoc
dnl
dnl Receive an invocation message and try to bind the process.
dnl
dnl The next rule should not be triggered anymore, because it is
dnl superseded by [transport-imsg] below.
dnl
dnl STEP(< O : C | Att: S`,' Pr: P`,' PrQ: W`,' Dealloc: LS`,'
dnl            Ev: MM + invoc(O'`,' Lab`,' Q`,' DL)`,' Lcnt: N >,
dnl   < O : C | Att: S`,' Pr: P`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
dnl     bindMtd(O`,' O'`,' Lab`,' Q`,' DL`,' C < emp >),
dnl `[label receive-invoc]')
dnl
dnl
dnl STEP(< O : C | Att: S`,' Pr: P`,' PrQ: W`,' Dealloc: LS`,'
dnl             Ev: MM + invoc(O'`,' Lab`,' Q @ CC`,' DL)`,' Lcnt: N >,
dnl   < O : C | Att: S`,' Pr: P`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
dnl     bindMtd(O`,' O'`,' Lab`,' Q`,' DL`,' CC < emp >),
dnl `[label receive-static-invoc]')


--- Method binding with multiple inheritance
---
eq
  bindMtd(O, O', Lab, Q, DL, (C < EL >) ,, I')
  < C : Cl | Inh: I , Par: AL, Att: S , Mtds: MS , Ocnt: F >
  =
  if get(Q, C, MS, O', Lab, DL) == notFound then
    bindMtd(O, O', Lab, Q, DL, I ,, I')
  else
    boundMtd(O, get(Q, C, MS, O', Lab, DL))
  fi
  < C : Cl | Inh: I , Par: AL, Att: S , Mtds: MS , Ocnt: F >
  .

eq
  boundMtd(O, P')
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  < O : C | Att: S, Pr: P, PrQ: W ++ P', Dealloc: LS, Ev: MM, Lcnt: N >
  .

--- receive-comp
---
--- Must be a rule in the model checker, because there might be multiple
--- completion messages with the same label but different return values
--- in the queue.
---
rl
  < O : C |  Att: S, Pr: (L, (Lab ? (AL)) ; SL), PrQ: W, Dealloc: LS,
             Ev: MM  + comp(Lab, DL), Lcnt: F > 
  =>
  < O : C |  Att: S, Pr: (L, assign(AL, DL) ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label receive-comp] .


--- local-reply
---
CSTEP(dnl
< O : C | Att: S`,' Pr: (L`,' Lab ?(AL); SL)`,' PrQ: W ++ (L'`,' SL1)`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >,
< O : C | Att: S`,' Pr: (L'`,' SL1 ; cont(Lab))`,'
  PrQ: W ++ (L`,' Lab ?(AL); SL)`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >,
L'[".label"] == Lab,
`[label local-reply]')


--- continue
---
--- Continue after executing the code of a local reply.  This is always a
--- rule.  We want it to be a rule in the interpreter.  It must be a rule
--- in the model checker, because there might be two processes in PrQ
--- which await a reply to the label.
rl
  < O : C | Att: S, Pr: (L, cont(Lab)), PrQ: W ++ (L', (Lab ?(AL); SL1)),
    Dealloc: LS, Ev: MM, Lcnt: F >
  =>
  < O : C | Att: S, Pr: (L', (Lab ?(AL); SL1)), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label continue] .


--- local-async-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: (L, (A ! Q(EL)); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  =
  < O : C | Att: S, Pr: (insert(A, label(O, O, Q, EVALLIST(EL, (S :: L), T)), L), SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  bindMtd(O, O, label(O, O, Q, EVALLIST(EL, (S :: L), T)), Q, EVALLIST(EL, (S :: L), T), C < emp >) CLOCK'
,
`rl
  < O : C | Att: S, Pr: (L, (A ! Q(EL)); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: (insert(A, label(O, N), L), SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N + 1 >  CLOCK
  invoc(O, label(O, N), Q, EVALLIST(EL, (S :: L), T)) from O to O'
)dnl
  [label local-async-call] .


--- local-async-static-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: (L, ( A ! (Q @ CC) (EL) ); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  CLOCK
  =
  < O : C | Att: S, Pr: (insert(A, label(O, O, Q, EVALLIST(EL, (S :: L), T)), L), SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O`,' O`,' label(O, O, Q, EVALLIST(EL, (S :: L), T))`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
,
`rl
  < O : C | Att: S, Pr: (L, ( A ! Q @ CC(EL)); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: (insert (A, label(O, N), L), SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N + 1 >
  bindMtd(O`,' O`,' label(O, N)`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
)dnl
  [label local-async-static-call] .


--- remote-async-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: (L, (A ! E . Q(EL)); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =
  < O : C | Att: S, Pr: (insert(A, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), L), SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  invoc(O, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), Q, EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
,dnl
`rl
  < O : C | Att: S, Pr: (L, (A ! E . Q(EL)); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: (insert(A, label(O, N), L), SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N + 1 > CLOCK
  invoc(O, label(O, N), Q , EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
)dnl
  [label remote-async-call] .


--- return
---
STEP(`< O : C |  Att: S, Pr: (L, (return(EL)); SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
`< O : C |  Att: S, Pr: (L, SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  comp(L[".label"], EVALLIST(EL, (S :: L), T)) from O to caller(L[".label"])',
`[label return]')


--- transport
---
--- Transport rule: include new message in queue
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  cmsg from O' to O
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM + cmsg, Lcnt: N >
  [label transport-cmsg] .

eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  invoc(O', Lab, Q, DL) from O' to O
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O, O', Lab, Q, DL, C < emp >)
  [label transport-imsg] .

--- free
---
--- Free a label.  Make sure that the use of labels is linear.
---
STEP(< O : C | Att: S`,' Pr: (L`,' free(A) ; SL)`,' PrQ: W`,'
               Dealloc: LS`,' Ev: MM`,' Lcnt: N >,
  < O : C | Att: S`,' Pr: (insert(A`,' null`,' L)`,' SL)`,' PrQ: W`,'
            Dealloc: (L[A] ^ LS)`,' Ev: MM`,' Lcnt: N >,
  `[label free]')


--- deallocate
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: (Lab ^ LS),
            Ev: MM + comp(Lab, DL), Lcnt: N >
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  [label deallocate] .


--- TAIL CALLS
---
--- Fake the caller and the label and tag the label.  Since we do not
--- want to interleave, this can also be an equation.
---
STEP(`< O : C | Att: S, Pr: (L, tailcall Q(EL) ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`< O : C | Att: S, Pr: (noSubst, accept(tag(L[".label"]))), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), C < emp >)'
  CLOCK,
`[label tailcall]')

STEP(`< O : C | Att: S, Pr: (L, tailcall Q @ CC (EL) ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`< O : C | Att: S, Pr: (noSubst, accept(tag(L[".label"]))), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), CC < emp >)'
  CLOCK,
`[label tailcall-static]')

*** If we receive the method body, the call is accepted and the label untagged.
crl
  < O : C | Att: S, Pr: (noSubst, accept(Lab)), PrQ: W ++ (L, SL),
         Dealloc: LS, Ev: MM, Lcnt: N >
  =>
  < O : C | Att: S, Pr: (insert(".label", tag(Lab), L), SL), PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: N >
  if L[".label"] = Lab
  [label tailcall-accept] .


--- OBJECT CREATION
---
--- Set up an init process, which is essentially init(;); !run()
---
--- It is smarter to invoke the run method asynchronously from the
--- initialisation process, to make sure that
--- the initialisation process will terminate instead of waiting for the
--- return of run in ill-behaved programs.  We cannot use a tail-call
--- here, because there is no caller the initialisation will return to.
---
STEP(dnl
< O : C | Att: S`,'Pr: (L`,' (A ::= new CC (EL)); SL)`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N > 
  < CC : Cl | Inh: I `,' Par: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: F >
  CLOCK`'dnl
,dnl
< O : C | Att: S`,' Pr: (L`,' assign(A`,' newId(CC`,' F)); SL)`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  < CC : Cl | Inh: I `,' Par: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: (F + 1) >
  < newId(CC`,'F) : CC | Att: S`,' Pr: idle`,' PrQ: noProc`,' Dealloc: noDealloc`,' Ev: noMsg`,' Lcnt: 0 >
  findAttr(newId(CC`,' F)`,' I`,' S'`,' 
    assign(AL`,' EVALLIST(EL, compose(S`,'  L), T))`,'
    ((noSubst`,' (".anon" ! "init" (emp)) ; (".anon" ?(noVid)) ;
    (".anon" ! "run" (emp)) ; free(".anon")))) CLOCK,dnl
`[label new-object]')


--- ATTRIBUTE inheritance with multiple inheritance
--- CMC assumes that all attributes names are (globally) different.
--- For the purpose of the CMC the class parameters are treated as
--- attributes!
---
op findAttr  : Oid InhList Subst StmList Process -> Msg [ctor `format' (n d)] .
op foundAttr : Oid Subst  StmList Process -> Msg [ctor `format' (n d)] .

eq findAttr(O, noInh, S, SL, P) = foundAttr(O, S, SL, P) .

--- The initialisation of the attributes is ordered from class to
--- super-class, because we want to pass on the class parameters to
--- the super-class.  The initialisation, i.e., calling the init method,
--- is done from the super classes to the sub-classes, making sure that
--- the state of the object at the beginning of the init call is in a
--- consistent state.
---
eq
  findAttr(O,(C < EL > ,, I'), S, SL, (L', SL1)) 
  < C : Cl | Inh: I, Par: AL, Att: S', Mtds: MS, Ocnt: F >
  =
  findAttr(O, I' ,, I, compose(S', S),
           SL ; (AL ::= EL), 
           (L', (".init" ! "init" @ C(emp)) ; (".init" ?(noVid)) ; SL1))
  < C : Cl | Inh: I, Par: AL, Att: S', Mtds: MS, Ocnt: F > .

eq
  foundAttr(O, S', SL, (L', SL1))
  < O : C | Att: S, Pr: idle, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  < O : C | Att: ("this" |-> O, S'), Pr: (L', SL ; SL1), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > .



--- REAL-TIME CREOL
---
--- posit
---
ifdef(`TIME',dnl
`CSTEP(
`< O : C | Att: S, Pr: (L, posit G ; SL), PrQ: W,
           Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
`< O : C | Att: S, Pr: (L, SL) , PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
EVALGUARD(G, (S :: L), MM, T) asBool,
`[label posit]')',
`STEP(
`< O : C | Att: S, Pr: (L, posit G ; SL), PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`< O : C | Att: S, Pr: (L,SL) , PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`[label posit]')'dnl
)dnl END if time.


ifdef(`TIME',dnl
--- The following formalises the tick rule for real-time Creol.  This rule
--- is only enabled if and only if all posit constraints are satisfied in
--- the global state at the new time.

op posit(_,_,_) : Subst StmList Float -> Bool .
eq posit(S, posit E ; SL, T) = EVAL(E, S, T) asBool .
eq posit(S, (SL1 [] SL2); SL, T) = posit(S, SL1, T) or posit(S, SL2, T) .
eq posit(S, (SL1 ||| SL2); SL, T) = posit(S, SL1, T) or posit(S, SL2, T) .
eq posit(S, SL, T) = true [owise] .

op posit(_,_,_) : Subst MProc Float -> Bool .
eq posit(S, W ++ idle, T) = posit(S, W, T) .
eq posit(S, W ++ (L, SL), T) = posit((S :: L), SL, T) and posit(S, W, T) .
eq posit(S, noProc, T) = true .

op posit : Configuration Float -> Bool .
eq posit (c:Class cnf, T) = posit (cnf, T) .
eq posit (< O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > cnf, T) =
    posit (S, W ++ P, T) and posit (cnf, T) .
eq posit (noConf, T) = true .

*** A very simple discrete time clock.
crl
  { cnf < T : Clock | delta: delta > }
  =>
  { cnf < T + delta : Clock | delta: delta >  }
  if posit (cnf, T + delta)
  [label tick] .
)dnl

endm

ifdef(`MODELCHECK',dnl
*** The predicates we can define on configurations.
mod CREOL-PREDICATES is
  protecting CREOL-SIMULATOR .
  ops objcnt maxobjcnt minobjcnt : String Nat -> Prop .
  op hasvalue : Oid Vid Data -> Prop .
  var A : Vid .
  var D : Data .
  var C : String .
  var O : Oid .
  vars S S' L L' : Subst .
  var LS : Labels .
  var MM : MMsg .
  var P : Process .
  var Q : MProc .
  vars N N' : Nat .
  var c : Configuration .

  eq { c < C : Cl | Inh: I:InhList`,' Par: AL:VidList`,' Att: S`,' Mtds: M:MMtd`,' Ocnt: N > } |= objcnt(C`,' N') = N == N' .
  eq { c < C : Cl | Inh: I:InhList`,' Par: AL:VidList`,' Att: S`,' Mtds: M:MMtd`,' Ocnt: N > } |= maxobjcnt(C`,' N') = N <= N' .
  eq { c < C : Cl | Inh: I:InhList`,' Par: AL:VidList`,' Att: S`,' Mtds: M:MMtd`,' Ocnt: N > } |= minobjcnt(C`,' N') = N >= N' .
  eq { c < O : C | Att: S`,' Pr: P`,' PrQ: Q`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N > } |= hasvalue(O`,' A`,' D) = D == S[A] .

endm
)dnl

eof
