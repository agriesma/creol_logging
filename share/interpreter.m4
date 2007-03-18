dnl
dnl interpreter.m4 -- Source for modelchecker.maude and interpreter.maude
dnl
dnl Copyright (c) 2007 Marcel Kyas
dnl
dnl The purpose of this file is to create the files `interpreter.maude'
dnl and `modelchecker.maude'.  These files have to be processed with
dnl m4, with either one of `CREOL' or `MODELCHECK' defined.
dnl
changequote({|,|})dnl
dnl
dnl The macro STEP is used to indicate that the specified transition
dnl may be both an equation (this is the case for model checking,
dnl or a rule (in the interpreter).
dnl $1 is the pre-condition of the rule.
dnl $2 is the post-condition of the rule.
dnl $3 is an annotation.  It must not be empty, and usually contains at
dnl    least the label.
define({|STEP|},dnl
ifdef({|MODELCHECK|},
{|eq
  $1
  =
  $2
  $3 .|},
{|rl
  $1
  =>
  $2
  $3 .|}))dnl
dnl
dnl The macro CSTEP is used to indicate that the specified transition
dnl may be both a conditional equation (this is the case for model checking),
dnl or a conditional rule (in the interpreter).
dnl $1 is the pre-condition of the rule.
dnl $2 is the post-condition of the rule.
dnl $3 is the condition.
dnl $4 is an annotation.  It must not be empty, and usually contains at
dnl    least the label.
define({|CSTEP|},dnl
ifdef({|MODELCHECK|},
{|ceq
  $1
  =
  $2
  if $3
  $4 .|},
{|crl
  $1
  =>
  $2
  if $3
  $4 .|}))dnl
dnl The usual header.
***
ifdef({|MODELCHECK|},dnl
{|*** Modelchecker for Creol.|},dnl
{|*** Reimplementation of the CREOL interpreter, 2007|})
***
*** Copyright (c) 2007
***
*** Do NOT edit this file.  This file may be overwritten.  It has been
*** automatically generated from interpreter.m4 using m4.
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

load datatypes

load signature

*** THE MACHINE ***
mod ifdef({|MODELCHECK|},MODEL-CHECKER,INTERPRETER) is

  extending CREOL-DATA-SIG .

  op label : Nat -> Label [ctor] .

  protecting AUX-FUNCTIONS .

  vars O O' : Oid .
  vars C C' : Cid .
  vars A A' : Aid .
  var AL : AidList .
  var NeAL : NeAidList .
  var D : Data .
  var DL : DataList .
  var NeDL : NeDataList .
  vars E E' : Expr .
  vars EL EL' : ExprList .
  vars NeEL NeEL' : NeExprList .
  var ST : Stm .
  vars SL SL' SL'' : StmList .
  vars SL1 SL2 : NeStmList .
  var P : Process .
  var W : MProc .
  vars S S' L L' : Subst .
  vars N F : Nat .
  vars I I' : InhList .
  var MS : MMtd .
  vars Lab Lab' : Label .
  var LS : Labels .
  var MM : MMsg .
  var G : Guard .
  var M : Mid .
  var Q : Qid .
  var MsgBody : Body .

*** multiple assignment
***
*** For the model checker the following will be evaluated as an
*** equation and the old rule is not confluent.

op _assign_ : AidList DataList -> Stm [ctor format (d c o d)] .
eq noAid assign emp = skip . *** Occurs during construction and returns.

eq
  < O : C | Att: S, Pr: (L, AL ::= EL ; SL),
	    PrQ: W, Lcnt: N >
  =
  < O : C | Att: S, Pr: (L,((AL assign evalList(EL, (S {|#|} L))); SL)), 
	    PrQ: W, Lcnt: N > .

STEP({|< O : C | Att: S, Pr: (L,( (A ,, NeAL assign D # NeDL) ; SL)), PrQ: W, Lcnt: N >|},
{|if dom(A,S) then
    < O : C | Att: insert(A, D, S), Pr: (L, (NeAL assign NeDL) ; SL), PrQ: W, Lcnt: N > 
  else
    < O : C | Att: S, Pr: (insert(A, D, L), (NeAL assign NeDL) ; SL), PrQ: W, Lcnt: N > 
  fi|},
{|[label assign]|})

STEP({|< O : C | Att: S, Pr: (L,( (A assign D) ; SL)), PrQ: W, Lcnt: N >|},
{|if dom(A,S) then
    < O : C | Att: insert(A, D, S), Pr: (L, SL), PrQ: W, Lcnt: N > 
  else
    < O : C | Att: S, Pr: (insert(A, D, L), SL), PrQ: W, Lcnt: N > 
  fi|},
{|[label assign]|})

STEP(dnl
{|< O : C | Att: S, Pr: (L, skip ; SL), PrQ: W, Lcnt: N >|},
{|< O : C | Att: S, Pr: (L, SL), PrQ: W, Lcnt: N >|},
{|[label skip]|})


*** if_then_else ***
STEP(dnl
{|< O : C | Att: S, Pr: (L, if E th SL' el SL'' fi ; SL), PrQ: W, Lcnt: N >|},
{|if {|eval|}(E, (S {|#|} L)) asBool then
    < O : C | Att: S, Pr: (L, SL' ; SL), PrQ: W, Lcnt: N >
  else
    < O : C | Att: S, Pr: (L, SL'' ; SL), PrQ: W, Lcnt: N >
  fi|},
{|[label if-th]|})

*** while ***
*** During model checking we want to be able to observe infinite loops.
*** Therefore, this has to be a rule.
rl
  < O : C | Att: S, Pr: (L, while E do SL1 od ; SL2), PrQ: W, Lcnt: N >
  =>
  < O : C | Att: S,
            Pr: (L, (if E th (SL1 ; while E do SL1 od) el skip fi); SL2),
            PrQ: W, Lcnt: N >
  [label while] .

*** OBJECT CREATION
***
*** Using synchronous calls does not work for the model checker.
*** Expanding 'init(emp:noAid) needs a label value, which we do
*** not have.  We reserve a label for our purposes.
STEP(dnl
{|< O : C | Att: S,Pr: (L, (A ::= new C' (EL)); SL),PrQ: W, Lcnt: N > 
  < C' : Cl | Inh: I , Par: AL, Att: S' , Mtds: MS , Ocnt: F >|},
{|< O : C | Att: S, Pr: (L, (A assign newId(C', F)); SL), PrQ: W, Lcnt: N >
  < C' : Cl | Inh: I , Par: AL, Att: S' , Mtds: MS , Ocnt: (F + 1) >
  < newId(C',F) : C' | Att: S, Pr: idle, PrQ: noProc, Lcnt: 1 >
  < newId(C',F) : Qu | Dealloc: noDealloc, Ev: noMsg > 
  findAttr(newId(C',F), I, S', 
    (AL assign evalList(EL, (S {|#|} L))),
    ((noSubst, (C ! 'init (emp)) ; (C ?(noAid)) ; (C ! 'run (emp)) ; (C ?(noAid)))))|},
{|[label new-object]|})


*** ATTRIBUTE inheritance with multiple inheritance
*** CMC assumes that all attributes names are (globally) different

op findAttr  : Oid InhList Subst StmList Process -> Msg [ctor format (n d)] .
op foundAttr : Oid Subst  StmList Process -> Msg [ctor format (n d)] .

eq findAttr(O, noInh, S, SL, P) = foundAttr(O, S, SL, P) .

*** Good thing we cannot use class names as variables in (at least in
*** the source language.  The name of the class will be used as the
*** name of the variable used to call the init routine.
***
*** XXX: Why is the call prepended, shouldn't it be appended?
eq
  findAttr(O,((C < EL >) {|#|}{|#|} I),S, SL, (L', SL')) 
  < C : Cl | Inh: I', Par: AL, Att: L, Mtds: MS, Ocnt: F >
  =
  findAttr(O, I {|#|}{|#|} I',(L {|#|} S), (AL ::= EL) ; SL, 
           (L', (C ! 'init @ C(emp)) ; (C ?( noAid)) ; SL'))
  < C : Cl | Inh: I', Par: AL, Att: L, Mtds: MS, Ocnt: F > .

eq
  foundAttr(O, S', SL, (L', SL'))
  < O : C | Att: S, Pr: idle, PrQ: W, Lcnt: N >
  =
  < O : C | Att: ('this |-> O, S'), Pr: (L', SL ; SL'), PrQ: W, Lcnt: N >
  .





*** Non-deterministic choice ***
*** Choice is comm, so [nondet] considers both SL1 and SL2.
CSTEP(dnl
{|< O : C | Att: S, Pr: (L, (SL1 [] SL2); SL), PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM >|},
{|< O : C | Att: S, Pr: (L, (SL1 ; SL)), PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM >|},
{| ready(SL1, (S # L), MM)|},
{|[label nondet]|})




*** Merge ***
*** Merge is comm, so [merge] considers both SL1 and SL2.
crl
  < O : C | Att: S, Pr: (L, (SL1 ||| SL2); SL), PrQ: W, Lcnt: N >  
  < O : Qu | Dealloc: LS, Ev: MM >
  =>
  < O : C | Att: S, Pr: (L, (SL1 MERGER SL2); SL), PrQ: W, Lcnt: N >  
  < O : Qu | Dealloc: LS, Ev: MM >
  if ready(SL1,(S {|#|} L), MM)
  [label merge] .

rl
  < O : C | Att: S,  Pr:  (L, ((ST ; SL') MERGER SL2); SL), PrQ: W, Lcnt: N >   
  < O : Qu | Dealloc: LS, Ev: MM >
  =>
  if enabled(ST,(S {|#|} L), MM) then
    < O : C | Att: S, Pr: (L, ((ST ; (SL' MERGER SL2)); SL)), PrQ: W, Lcnt: N >   
  else
    < O : C | Att: S, Pr: (L, ((ST ; SL') ||| SL2); SL), PrQ: W, Lcnt: N >   
  fi
  < O : Qu | Dealloc: LS, Ev: MM >
  [label merge-aux] .

STEP(dnl
{|< O : C | Att: S, Pr: (L, (cont(Lab) MERGER SL'); SL''), 
            PrQ: (L', ((Lab ?(A)); SL)) ++ W, Lcnt: F >|},
{|< O : C | Att: S, Pr: (L',((((Lab ?(A)) ; SL) MERGER SL'); SL'')), 
            PrQ: W, Lcnt: F >|},
{|[label continue2]|})

*** local call 
ceq
  boundMtd(O, (L', SL')) 
  < O : C | Att: S,Pr: (L, ((Lab ?(AL)); SL)),PrQ: W,Lcnt: F >
  = 
  < O : C | Att: S,Pr: (L', SL' ; cont(Lab)),PrQ: (L,((Lab ?(AL)); SL)) ++ W,
            Lcnt: F > 
  if (L'['label] == Lab)
  [label local-call] .

*** local call within merge
ceq
  boundMtd(O, (L', SL')) 
  < O : C | Att: S,Pr: (L,(((Lab ?(AL)); SL) MERGER SL'')),PrQ: W,Lcnt: F >
  = 
  < O : C | Att: S,Pr: (L', SL'),
       PrQ: (L, (((await Lab ?) ; (Lab ?(AL)); SL) MERGER SL'')) ++ W,Lcnt: F > 
  if (L'['label] == Lab)
  [label local-call-in-merge] .

*** Suspension ***

CSTEP(dnl
{|< O : C | Att: S, Pr: (L,SL), PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM >|},
{|< O : C | Att: S, Pr: idle, PrQ: W ++ (L, SL), Lcnt: N > *** clear(SL)
  < O : Qu | Dealloc: LS, Ev: MM >|},
{|not enabled(SL, (S # L), MM)|},
{|[label suspend]|})

*** Guards ***

CSTEP(dnl
{|< O : C | Att: S, Pr: (L, await G ; SL), PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM >|},
{|< O : C | Att: S, Pr: (L,SL) , PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM > |},
{|enabledGuard(G, (S # L), MM)|},
{|[label guard]|})

*** Evaluate guards in suspended processes ***

*** Must be a rule, also in the interpreter.
crl
  < O : C | Att: S, Pr: idle, PrQ: (L,SL) ++ W, Lcnt: N > 
  < O : Qu | Dealloc: LS, Ev: MM >
  => 
  < O : C | Att: S, Pr: (L,SL), PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM >
  if ready(SL, (S {|#|} L), MM) 
  [label PrQ-ready] .


eq
  < O : C | Att: S, Pr: idle, PrQ: (L, await wait ; SL) ++ W, Lcnt: N >  
  =
  < O : C | Att: S, Pr: idle, PrQ: (L, SL) ++ W, Lcnt: N > [label wait] .

eq
  < O : C | Att: S, Pr: idle, PrQ: (L, ((await wait ; SL)[] SL'); SL'')++ W,  
    Lcnt: N >  
  =
  < O : C | Att: S, Pr: idle, PrQ: (L, (SL [] SL'); SL'') ++ W, Lcnt: N >
[label wait-nondet] .

eq
  < O : C | Att: S, Pr: idle, PrQ: (L,((await wait ; SL)||| SL'); SL'')++ W,  
    Lcnt: N >  
  =
  < O : C | Att: S, Pr: idle, PrQ: (L, (SL ||| SL'); SL'') ++ W, Lcnt: N >
  [label wait-merge] .





*** Optimization to avoid muiltiple lookups in the message queue for
*** the same guard
eq 
  < O : C | Att: S, Pr: P, PrQ: (L, await (Lab ? & G); SL) ++ W, Lcnt: F > 
  < O : Qu | Dealloc: LS, Ev: MM + comp(Lab, DL) >  
  =
  < O : C | Att: S,  Pr: P, PrQ: (L, await G ; SL) ++ W, Lcnt: F >    
  < O : Qu | Dealloc: LS, Ev: MM + comp(Lab, DL) > .


***
*** Tail calls.
***
*** Fake the caller and the label and tag the label.  Since we do not
*** want to interleave, this can also be an equation.
STEP({|< O : C | Att: S, Pr: (L, tailcall M(EL) ; SL), PrQ: W, Lcnt: N >|},
{|< O : C | Att: S, Pr: (noSubst, accept(tag(L['label]))), PrQ: W, Lcnt: N >
 bindMtd(O, L['caller], tag(L['label]), M, evalList(EL, (S # L)), C < emp >)
|},
{|[label tailcall]|})

*** If we receive the method body, the call is accepted and the label untagged.
CSTEP({|< O : C | Att: S, Pr: (noSubst, accept(Lab)), PrQ: W, Lcnt: N >
  boundMtd(O, (L, SL))|},
{|< O : C | Att: S, Pr: (insert('label, tag(Lab), L), SL), PrQ: W, Lcnt: N >|},
{|L['label] = Lab|},
{|[label tailcall-accept]|})





*** METHOD CALLS ***

eq   ! Q(EL) =   ! 'this . Q(EL) . *** could alternatively use X@ this class

*** receive invocation message ***
STEP({|< O : C | Att: S, Pr: P, PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM + invoc(O', Lab, Q, DL) >|},
{|< O : C | Att: S, Pr: P, PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM > bindMtd(O, O', Lab, Q, DL, C < emp >)|},
{|[label receive-call-req]|})

*** Method binding with multiple inheritance
ceq bindMtd(O, O',Lab,Q, EL,noInh) = 
boundMtd(O,(('caller |-> O', 'label |-> Lab), return(emp)))
if Q == 'run .


eq bindMtd(O, O', Lab, M, EL, (C < EL' >) {|#|}{|#|} I')
< C : Cl | Inh: I , Par: AL, Att: S , Mtds: MS , Ocnt: F >
   =  if (M in MS) then boundMtd(O,get(M,MS,O', Lab, EL)) 
                   else bindMtd(O,O',Lab,M,EL, I {|#|}{|#|} I') fi 
< C : Cl | Inh: I , Par: AL, Att: S , Mtds: MS , Ocnt: F > .

STEP({|< O : Qu | Dealloc: LS, Ev: MM + invoc(O', Lab, Q @ C, DL) >|},
{|< O : Qu | Dealloc: LS, Ev: MM >
    bindMtd(O, O', Lab, Q, DL, C < emp >)|},
{|[label receive-call-req]|})

STEP({|boundMtd(O, P) < O : C | Att: S, Pr: idle, PrQ: W, Lcnt: N >|},
{|< O : C | Att: S, Pr: idle, PrQ: W ++ P, Lcnt: N >|},
{|[label receive-call-bound]|})

STEP({|< O : C | Att: S, Pr: (L, cont(Lab); SL), PrQ: (L',((Lab)?(AL); SL')) ++
    W, Lcnt: F >|},
{|< O : C | Att: S, Pr: (L',(Lab)?(AL); SL'), PrQ: W, Lcnt: F >|}
{|[label continue]|})

STEP({|< O : C | Att: S, Pr: (L, ( ! Q @ C'(EL)); SL),PrQ: W, Lcnt: N >|},
{|< O : C | Att: S, Pr: (L, SL), PrQ: W, Lcnt: N + 1 >
invoc(O, label(N), Q @ C', evalList(EL, (S # L))) from O to O |},
{|[label local-async-qualified-req]|})

*** REMOTE METHOD CALLS ***
eq < O : C | Att: S, Pr: (L, (Q ! M(EL)); SL), PrQ: W, Lcnt: N >
=  < O : C | Att: S, Pr: (L, (Q assign label(N)); (! M (EL));  SL), 
             PrQ: W,  Lcnt: N > .


STEP({|< O : C | Att: S, Pr: (L, ( ! E . M(EL)); SL), PrQ: W, Lcnt: N >|},
{|< O : C | Att: S, Pr: (L,SL), PrQ: W, Lcnt: N + 1 >
  invoc(O, label(N), M , evalList(EL, (S # L)))
    from O to {|eval|}(E, (S # L))|},
{|[label remote-async-reply]|})

*** Reduce sync. call  to async. call with reply 
*** XXX: This rule will eventually go away once the compiler does this
*** expansion.
eq < O : C | Att: S, Pr: (L, (M(EL : AL)); SL), PrQ: W, Lcnt: N >
  =
  < O : C | Att: S, Pr: (L, (! M(EL)); (label(N) ?(AL)); SL), PrQ: W,  Lcnt: N >  .

*** emit reply message ***
STEP({|< O : C |  Att: S, Pr: (L, (return(EL)); SL), PrQ: W, Lcnt: N >|},
{|< O : C |  Att: S, Pr: (L, SL), PrQ: W, Lcnt: N >
  comp(L['label], evalList(EL, (S # L))) from O to L['caller]|},
{|[label return]|})

*** Optimization: reduce label to value only once
eq
  < O : C |  Att: S, Pr: (L, (A ?(AL)); SL), PrQ: W, Lcnt: N > 
  =
  < O : C |  Att: S, Pr: (L, ((L[A]) ?(AL)); SL), PrQ: W, Lcnt: N > .


*** Model checker behaves differently from interpreter in that receiving
*** and freeing of label variables will set the variable containing this
*** name to null.  This will save us some states.  In the model checker
*** it is /guaranteed/ that exactly one variable exists, which holds the
*** label value,
eq
  < O : C |  Att: S,
    Pr: ((ifdef({|MODELCHECK|}, {|A |-> Lab, L|}, L)),
         (Lab ? (AL)); SL), PrQ: W, Lcnt: F > 
  < O : Qu | Dealloc: LS, Ev: MM + comp(Lab, DL) >
  = 
  < O : C |  Att: S,
    Pr: ((ifdef({|MODELCHECKER|}, {|A |-> null, L|}, L)),
         (AL assign DL); SL), PrQ: W, Lcnt: F > 
  < O : Qu | Dealloc: LS, Ev: MM >
  .

*** Transport rule: include new message in queue
STEP({|< O : Qu | Dealloc: LS, Ev: MM > (MsgBody from O' to O)|},
  {|< O : Qu | Dealloc: LS, Ev: MM + MsgBody >|},
  {|[label invoc-msg]|})

*** Free a label.
STEP({|< O : C | Att: S, Pr: (L, free(A) ; SL), PrQ: W, Lcnt: N >
  < O : Qu | Dealloc: LS, Ev: MM >|},
  {|< O : C | Att: S, Pr: (L,SL), PrQ: W, Lcnt: N > 
  < O : Qu | Dealloc: ({|eval|}(A, (S # L)) ; LS), Ev: MM >|},
  {|[label free]|})

*** Deallocate
eq
  < O : Qu | Dealloc: (Lab ^ LS), Ev: comp(Lab , DL) + MM >
  =
  < O : Qu | Dealloc: LS, Ev: MM >
  [label deallocate] .

endm

eof