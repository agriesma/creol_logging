dnl
dnl machine.m4 -- The specification of the machine.
dnl
dnl Copyright (c) 2007, 2008
dnl
dnl The purpose of this file is to create the files `interpreter.maude'
dnl and `modelchecker.maude'.  These files have to be processed with
dnl m4, with either one of `CREOL' or `MODELCHECK' defined.
dnl
dnl See the lines below for its license
dnl
*** The machine.
***
mod CREOL-SIMULATOR is

  protecting `CREOL-EVAL' .

  op simurev : -> String .
  eq simurev = "KIND $Revision: 1466 $" .

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
`< O : C | Att: S, Pr: { L | assign(AL ; EL) ; SL },
	    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`< O : C | Att: S, Pr: { L | $assign(AL ; EVALLIST(EL, (S :: L), T)) ; SL }, 
	    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`[label assignment]')

eq
  < O : C | Att: S, Pr: { L | $assign((Q @ CC), AL ; D :: DL) ; SL },
    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
    < O : C | Att: insert(Q, D, S), Pr: { L | $assign(AL ; DL) ; SL },
      PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > 
  [label do-static-assign] .

eq
  < O : C | Att: S, Pr: { L | $assign( (Q, AL) ; D :: DL) ; SL },
    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  if $hasMapping(L, Q) then
    < O : C | Att: S, Pr: { insert(Q, D, L) | $assign(AL ; DL) ; SL },
      PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > 
  else
    < O : C | Att: insert(Q, D, S), Pr: { L | $assign(AL ; DL) ; SL },
      PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  fi
  [label do-assign] .



--- Skip
---
STEP(dnl
`< O : C | Att: S, Pr: { L | skip ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
   Lcnt: N >',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`[label skip]')


--- if_then_else
---
STEP(dnl
< O : C | Att: S`,' Pr: { L | if E th SL1 el SL2 fi ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  CLOCK,
if EVAL(E, (S :: L), T) asBool then
    < O : C | Att: S`,' Pr: { L | SL1 ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  else
    < O : C | Att: S`,' Pr: { L | SL2 ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  fi
  CLOCK,
`[label if-then-else]')


--- while
---
--- During model checking we want to be able to observe infinite loops.
--- Therefore, it is always a rule.
---
rl
  < O : C | Att: S, Pr: { L | while E do SL od ; SL1 }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =>
  < O : C | Att: S,
            Pr: { L | if E th (SL ; while E do SL od) el skip fi ; SL1 },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  [label while] .


--- Non-deterministic choice
---
--- Choice is comm, so [choice] considers both NeSL and NeSL1.
---
crl
  < O : C | Att: S, Pr: { L | (NeSL [] NeSL1); SL }, PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: { L | NeSL ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
            Lcnt: N > CLOCK
  if READY(NeSL, (S :: L), MM, T)
  [label choice] .


--- Merge
---
--- Merge is comm, so [merge] considers both NeSL and NeSL1.
---
crl
  < O : C | Att: S, Pr: { L | (NeSL ||| NeSL1); SL }, PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: { L | (NeSL MERGER NeSL1); SL }, PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: N > CLOCK
  if READY(NeSL,(S :: L), MM, T)
  [label merge] .

--- merger
---
eq
  < O : C | Att: S,  Pr:  { L | ((ST ; SL1) MERGER NeSL1); SL }, PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =
  if ENABLED(ST, (S :: L), MM, T) then
    < O : C | Att: S, Pr: { L | ((ST ; (SL1 MERGER NeSL1)); SL) }, PrQ: W,
      Dealloc: LS, Ev: MM, Lcnt: N >
  else
    < O : C | Att: S, Pr: { L | ((ST ; SL1) ||| NeSL1); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >   
  fi CLOCK
 [label merger] .


--- PROCESS SUSPENSION

--- release
---
--- The release statement is an unconditional processor release point.
---
STEP(dnl
`< O : C | Att: S, Pr: { L | release ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`< O : C | Att: S, Pr: idle, PrQ: W , { L | SL }, Dealloc: LS, Ev: MM, Lcnt: N >',
`[label release]')


--- suspend
---
CSTEP(dnl
`< O : C | Att: S, Pr: { L | SuS ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
`< O : C | Att: S, Pr: idle, PrQ: W , { L | SuS ; SL}, Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
not ENABLED(SuS, (S :: L), MM, T),
`[label suspend]')


--- await
---
CSTEP(dnl
`< O : C | Att: S, Pr: { L | await G ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
`EVALGUARD(G, (S :: L), MM, T) asBool'
`[label await]')

--- Optimize label access in await statements.
eq
  < O : C | Att: S, Pr: { L | await ?(A) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  < O : C | Att: S, Pr: { L | await ?(L[A]) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  .


--- Schedule a new process for execution, if it is ready.
---
--- Must be a rule to preserve confluence.
---
crl
  < O : C | Att: S, Pr: idle, PrQ: W , { L | SL }, Dealloc: LS, Ev: MM,
            Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  if READY(SL, (S :: L), MM, T)
  [label PrQ-ready] .


--- METHOD CALLS
---

--- OPTIMISATION: Reduce the value of a label in a process to avoid
--- constant re-evaluation
eq < O : C | Att: S, Pr: { L | get(A ; AL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > =
  < O : C | Att: S, Pr: { L | get(L[A] ; AL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > .


    --- Method binding messages.
    --- Bind method request
    --- Given: caller callee label method params (list of classes to look in)
    op bindMtd : Oid Oid Label String DataList InhList -> Msg
        [ctor `format'(!r d)] .

    --- Successfully bound method body. 
    --- Consider the call O.Q(I). bindMtd(O,Q,I,C S) tries to find Q in
    --- class C or superclasses, then in S. boundMtd(O,Mt) is the result.
    op boundMtd : Oid Process -> Msg [ctor `format'(!r d)] .

--- Method binding with multiple inheritance
---
eq
  bindMtd(O, O', Lab, Q, DL, (C < EL > , I'))
  < C : Class | Inh: I , Param: AL, Att: S , Mtds: MS , Ocnt: F >
  =
  if get(Q, C, MS, O', Lab, DL) == notFound then
    bindMtd(O, O', Lab, Q, DL, (I , I'))
  else
    boundMtd(O, get(Q, C, MS, O', Lab, DL))
  fi
  < C : Class | Inh: I , Param: AL, Att: S , Mtds: MS , Ocnt: F >
  .

eq
  boundMtd(O, P')
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  < O : C | Att: S, Pr: P, PrQ: (W , P'), Dealloc: LS, Ev: MM, Lcnt: N >
  .

  --- fetches pair (code, vars) to bind call to process.
  --- M represents the name of the method.
  --- C represents the name of the class.
  --- MM represents the methods we search through.
  --- O represents the identity of the caller.
  --- Lab represents the label used to return the value computed by the method.
  --- DL represents the list of actual arguments.
  op get : String String MMtd Oid Label DataList -> Process .
  eq get(Q, C, (MS, < Q : Method | Param: AL, Att: S, Code: SL >), O, Lab, DL)
    = { S, "caller" |-> O, ".class" |-> str(C), ".label" |-> Lab,
        ".method" |-> str(Q) | assign(AL ; DL) ; SL } .

  eq get(Q, C, MS, O, Lab, DL) = notFound [owise] .

--- receive-comp
---
--- Must be a rule in the model checker, because there might be multiple
--- completion messages with the same label but different return values
--- in the queue.
---
rl
  < O : C |  Att: S, Pr: { L | get(Lab ; AL) ; SL }, PrQ: W, Dealloc: LS,
             Ev: (MM  + comp(Lab, DL)), Lcnt: F > 
  =>
  < O : C |  Att: S, Pr: { L | assign(AL ; DL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label receive-comp] .


--- local-reply
---
CSTEP(dnl
< O : C | Att: S`,' Pr: { L | get(Lab ; AL) ; SL }`,' PrQ: W `,' { L' | SL1 }`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >,
< O : C | Att: S`,' Pr:  { L' | SL1 ; $cont(Lab) }`,'
  PrQ: W `,' { L | get(Lab ; AL) ; SL }`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >,
L'[".label"] == Lab,
`[label local-reply]')


--- continue
---
--- Continue after executing the code of a local reply.  This is always a
--- rule.  We want it to be a rule in the interpreter.  It must be a rule
--- in the model checker, because there might be two processes in PrQ
--- which await a reply to the label.
rl
  < O : C | Att: S, Pr: { L | $cont(Lab) }, PrQ: W , { L' | get(Lab ; AL) ; SL1},
    Dealloc: LS, Ev: MM, Lcnt: F >
  =>
  < O : C | Att: S, Pr: { L' | get(Lab ; AL) ; SL1 }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label continue] .


--- local-async-static-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; EL ); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, label(O, O, Q, EVALLIST(EL, (S :: L), T)), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O`,' O`,' label(O, O, Q, EVALLIST(EL, (S :: L), T))`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
,
`rl
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; EL ); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: { insert (A, label(O, N), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: (N + 1) >
  bindMtd(O`,' O`,' label(O, N)`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
)dnl
  [label local-async-static-call] .


--- remote-async-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  invoc(O, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), Q, EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
,dnl
`rl
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
  =>
  < O : C | Att: S, Pr: { insert(A, label(O, N), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: (N + 1) > CLOCK
  invoc(O, label(O, N), Q , EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
)dnl
  [label remote-async-call] .


--- return
---
STEP(`< O : C |  Att: S, Pr: { L | return(EL); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
`< O : C |  Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK
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
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: (MM + cmsg), Lcnt: N >
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
STEP(< O : C | Att: S`,' Pr: { L | free(A) ; SL }`,' PrQ: W`,'
               Dealloc: LS`,' Ev: MM`,' Lcnt: N >,
  < O : C | Att: S`,' Pr: { insert(A`,' null`,' L) | SL }`,' PrQ: W`,'
            Dealloc: (L[A] ^ LS)`,' Ev: MM`,' Lcnt: N >,
  `[label free]')


--- deallocate
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: (Lab ^ LS),
            Ev: (MM + comp(Lab, DL)), Lcnt: N >
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  [label deallocate] .


--- TAIL CALLS
---
--- Fake the caller and the label and tag the label.  Since we do not
--- want to interleave, this can also be an equation.
---
STEP(`< O : C | Att: S, Pr: { L | tailcall(Q ; EL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept(tag(L[".label"])) }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), C < emp >)'
  CLOCK,
`[label tailcall]')

STEP(`< O : C | Att: S, Pr: { L | tailcall(Q ; CC ; EL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept(tag(L[".label"])) }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), CC < emp >)'
  CLOCK,
`[label tailcall-static]')

*** If we receive the method body, the call is accepted and the label untagged.
crl
  < O : C | Att: S, Pr: { noSubst | $accept(Lab) }, PrQ: W , { L | SL },
         Dealloc: LS, Ev: MM, Lcnt: N >
  =>
  < O : C | Att: S, Pr: { insert(".label", tag(Lab), L) | SL }, PrQ: W,
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
< O : C | Att: S`,'Pr: { L | new (A ; CC ; EL); SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N > 
  < CC : Class | Inh: I `,' Param: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: F >
  CLOCK`'dnl
,dnl
< O : C | Att: S`,' Pr: { L | assign(A ; newId(CC`,' F)); SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: N >
  < CC : Class | Inh: I `,' Param: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: (F + 1) >
  < newId(CC`,'F) : CC | Att: S`,' Pr: idle`,' PrQ: noProc`,' Dealloc: noDealloc`,' Ev: noMsg`,' Lcnt: 0 >
  findAttr(newId(CC`,' F)`,' I`,' S'`,' 
    $assign(AL ; EVALLIST(EL, compose(S`,'  L), T))`,'
    { noSubst | call(".anon" ; "this" ; "init" ; emp) ; get(".anon" ; noVid) ;
    call (".anon" ; "this" ; "run" ; emp) ; free(".anon")}) CLOCK,dnl
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
  findAttr(O,(C < EL > , I'), S, SL, { L' | SL1 }) 
  < C : Class | Inh: I, Param: AL, Att: S', Mtds: MS, Ocnt: F >
  =
  findAttr(O, (I' , I), compose(S', S),
           SL ; assign(AL ; EL), 
           { L' | static(".init" ; "init" ; C ; emp) ; get(".init" ; noVid) ; SL1 })
  < C : Class | Inh: I, Param: AL, Att: S', Mtds: MS, Ocnt: F > .

eq
  foundAttr(O, S', SL, { L' | SL1 })
  < O : C | Att: S, Pr: idle, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  =
  < O : C | Att: ("this" |-> O, S'), Pr: { L' | SL ; SL1 }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > .



--- assert
---
STEP(dnl
`< O : C | Att: S, Pr: { L | assert(G) ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: N > CLOCK',
`if EVALGUARD(G, (S :: L), MM, T) asBool then
    < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >
  else
    < O : C | Att: S, Pr: { L | failure(G) ; SL }, PrQ: W, Dealloc: LS,
      Ev: MM, Lcnt: N >
  fi CLOCK',
`[label assert]')



--- REAL-TIME CREOL
---
--- posit
---
ifdef(`TIME',dnl
`CSTEP(
`< O : C | Att: S, Pr: { L | posit G ; SL }, PrQ: W,
           Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > CLOCK',
EVALGUARD(G, (S :: L), MM, T) asBool,
`[label posit]')',
`STEP(
`< O : C | Att: S, Pr: { L | posit G ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N >',
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
eq posit(S, (W , idle), T) = posit(S, W, T) .
eq posit(S, (W , { L | SL}), T) = posit((S :: L), SL, T) and posit(S, W, T) .
eq posit(S, noProc, T) = true .

op posit : Configuration Float -> Bool .
eq posit (c:Class cnf, T) = posit (cnf, T) .
eq posit (< O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: N > cnf, T) =
    posit (S, (W , P), T) and posit (cnf, T) .
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
