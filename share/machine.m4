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
fmod CREOL-SIMULATOR-BANNER is

    protecting STRING .
    op simurev : -> String .
    eq simurev = "KIND $Revision: 1466 $" .

endfm

*** The machine.
***
mod CREOL-SIMULATOR is

  protecting `CREOL-EVAL' .

  vars F G : Nat .                     --- Counters for generating fresh names.
  vars O O' : Oid .                    --- Object identifiers
  vars C CC : String .                 --- Class names
  vars Q Q' : String .                 --- Generic names (attribute and method)
  vars A A' : Vid .                    --- Generic attribute names
  var AL : VidList .                   --- List of LHS
  var N : Label .                      --- Call label
  var D : Data .                       --- Value
  vars DL DL2 : DataList .             --- List of values
  vars DS : DataSet .		       --- Set of data items.
  var E : Expr .                       --- Expression
  var EL : ExprList .                  --- List of Expressions
  var ST : Stmt .                      --- Statement
  var SST : SuspStmt .                 --- Suspendable statement
  vars S S' L L' : Subst .             --- Object and process states.
  vars SL SL1 SL2 : StmtList .         --- List of statements
  vars P P' : Process .
  var W : MProc .
  vars I I' : InhList .
  var MS : MMtd .
  var CN : Configuration .

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
 eq caller(label(O, F)) = O .
)dnl


    --- assignment
    ---
    --- Execute an assignment.  First, all expressions on the left hand side
    --- of the assignment are evaluated and the statement is rewritten to
    --- an assign form.
STEP(dnl
`< O : C | Att: S, Pr: { L | assign(AL ; EL) ; SL },
	    PrQ: W, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { L | $assign(AL ; EVALLIST(EL, (S :: L), T)) ; SL }, 
	    PrQ: W, Lcnt: F >' CLOCK,
`[label assignment]')

eq
  < O : C | Att: S, Pr: { L | $assign((Q @ CC), AL ; D :: DL) ; SL },
    PrQ: W, Lcnt: F >
  =
    < O : C | Att: insert(Q, D, S), Pr: { L | $assign(AL ; DL) ; SL },
      PrQ: W, Lcnt: F > 
  [label do-static-assign] .

eq
  < O : C | Att: S, Pr: { L | $assign( (Q, AL) ; D :: DL) ; SL },
    PrQ: W, Lcnt: F >
  =
  if $hasMapping(L, Q) then
    < O : C | Att: S, Pr: { insert(Q, D, L) | $assign(AL ; DL) ; SL },
      PrQ: W, Lcnt: F > 
  else
    < O : C | Att: insert(Q, D, S), Pr: { L | $assign(AL ; DL) ; SL },
      PrQ: W, Lcnt: F >
  fi
  [label do-assign] .



--- Skip
---
STEP(dnl
`< O : C | Att: S, Pr: { L | skip ; SL }, PrQ: W, Lcnt: F >',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >',
`[label skip]')


--- Commit a transaction.
    rl
      < O : C | Att: S, Pr: { L | commit ; SL }, PrQ: W, Lcnt: F >
      =>
      < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >
      [label commit] .

--- if_then_else
---
STEP(dnl
< O : C | Att: S`,' Pr: { L | if E th SL1 el SL2 fi ; SL }`,' PrQ: W`,' Lcnt: F >
  CLOCK,
if EVAL(E, (S :: L), T) asBool then
    < O : C | Att: S`,' Pr: { L | SL1 ; SL }`,' PrQ: W`,' Lcnt: F >
  else
    < O : C | Att: S`,' Pr: { L | SL2 ; SL }`,' PrQ: W`,' Lcnt: F >
  fi
  CLOCK,
`[label if-then-else]')


--- while
---
--- During model checking we want to be able to observe infinite loops.
--- Therefore, it is always a rule.
---
rl
  < O : C | Att: S, Pr: { L | while E do SL1 od ; SL }, PrQ: W, Lcnt: F >
  =>
  < O : C | Att: S,
            Pr: { L | if E th (SL1 ; while E do SL1 od) el skip fi ; SL },
            PrQ: W, Lcnt: F >
  [label while] .


--- Non-deterministic choice
---
--- Choice is comm, so [choice] considers both SL1 and SL2.
---
crl
  { < O : C | Att: S, Pr: { L | (SL1 [] SL2); SL }, PrQ: W, Lcnt: F > CN CLOCK }
  =>
  { < O : C | Att: S, Pr: { L | SL1 ; SL }, PrQ: W, Lcnt: F > CN CLOCK }
  if READY(SL1, (S :: L), CN, T)
  [label choice] .


ifdef(`WITH_MERGE',
`    --- Merge
    ---
    --- Merge is comm, so [merge] considers both SL1 and SL2.
    ---
    crl
      { < O : C | Att: S, Pr: { L | (SL1 ||| SL2); SL }, PrQ: W, 
                Lcnt: F > CN CLOCK }
      =>
      { < O : C | Att: S, Pr: { L | (SL1 MERGER SL2); SL }, PrQ: W, 
                Lcnt: F > CN CLOCK }
      if READY(SL1,(S :: L), CN, T)
      [label merge] .

    --- merger
    ---
    eq
      { < O : C | Att: S,  Pr:  { L | ((ST ; SL1) MERGER SL2); SL }, PrQ: W,
                Lcnt: F > CN CLOCK }
      =
      { if ENABLED(ST, (S :: L), CN, T) then
        < O : C | Att: S, Pr: { L | ((ST ; (SL1 MERGER SL2)); SL) }, PrQ: W,
          Lcnt: F >
      else
        < O : C | Att: S, Pr: { L | ((ST ; SL1) ||| SL2); SL }, PrQ: W, Lcnt: F >   
      fi CN CLOCK }
     [label merger] .')


--- PROCESS SUSPENSION

--- release
---
--- The release statement is an unconditional processor release point.
---
STEP(dnl
`< O : C | Att: S, Pr: { L | release ; SL }, PrQ: W, Lcnt: F >',
`< O : C | Att: S, Pr: idle, PrQ: W , { L | SL }, Lcnt: F >',
`[label release]')


--- suspend
---
CSTEP(dnl
`{ < O : C | Att: S, Pr: { L | SST ; SL }, PrQ: W, Lcnt: F > CN CLOCK }',
`{ < O : C | Att: S, Pr: idle, PrQ: W , { L | SST ; SL}, Lcnt: F > CN CLOCK }',
not ENABLED(SST, (S :: L), CN, T),
`[label suspend]')


--- await
---
CSTEP(dnl
`{ < O : C | Att: S, Pr: { L | await E ; SL }, PrQ: W, Lcnt: F > CN CLOCK }',
`{ < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F > CN CLOCK }',
`EVALGUARD(E, (S :: L), CN, T) asBool'
`[label await]')

--- Optimize label access in await statements.
eq
  < O : C | Att: S, Pr: { L | await ?(A) ; SL }, PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | await ?(L[A]) ; SL }, PrQ: W, Lcnt: F >
  .


--- Schedule a new process for execution, if it is ready.
---
--- Must be a rule to preserve confluence.
---
crl
  { < O : C | Att: S, Pr: idle, PrQ: W , { L | SL }, Lcnt: F > CN CLOCK }
  =>
  { < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F > CN CLOCK }
  if READY(SL, (S :: L), CN, T)
  [label PrQ-ready] .


--- METHOD CALLS
---

--- OPTIMISATION: Reduce the value of a label in a process to avoid
--- constant re-evaluation
eq < O : C | Att: S, Pr: { L | get(A ; AL) ; SL }, PrQ: W, Lcnt: F > =
  < O : C | Att: S, Pr: { L | get(L[A] ; AL) ; SL }, PrQ: W, Lcnt: F > .


--- receive-comp
---
--- Must be a rule in the model checker, because there might be multiple
--- completion messages with the same label but different return values
--- in the queue.
---
rl
  < O : C |  Att: S, Pr: { L | get(N ; AL) ; SL }, PrQ: W, Lcnt: F >
  comp(N, DL)
  =>
  < O : C |  Att: S, Pr: { L | assign(AL ; DL) ; SL }, PrQ: W, Lcnt: F >
  [label receive-comp] .


--- local-reply
---
CSTEP(dnl
`< O : C | Att: S, Pr: { L | get(N ; AL) ; SL }, PrQ: W , { L''` | SL1 }, Lcnt: F >',
`< O : C | Att: S, Pr:  { L''` | SL1 ; $cont N },
  PrQ: W , { L | get(N ; AL) ; SL }, Lcnt: F >',
L'[".label"] == N,
`[label local-reply]')


--- continue
---
--- Continue after executing the code of a local reply.  This is always a
--- rule.  We want it to be a rule in the interpreter.
--- 
--- If we support shared futures, this must be a rule in the model checker,
--- because there might be two processes in PrQ which await a reply to the
--- label.
rl
  < O : C | Att: S, Pr: { L | $cont N }, PrQ: W , { L' | get(N ; AL) ; SL1},
    Lcnt: F >
  =>
  < O : C | Att: S, Pr: { L' | get(N ; AL) ; SL1 }, PrQ: W,
    Lcnt: F >
  [label continue] .


--- local-async-static-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; "" ; EL ); SL }, PrQ: W, Lcnt: F >
  CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, label(O, O, Q, EVALLIST(EL, (S :: L), T)), L) | SL }, PrQ: W, Lcnt: F >
  bindMtd(O`,' O`,' label(O, O, Q, EVALLIST(EL, (S :: L), T))`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
,
`rl
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; "" ; EL ); SL }, PrQ: W, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { insert (A, label(O, F), L) | SL }, PrQ: W, Lcnt: (F + 1) >
  bindMtd(O`,' O`,' label(O, F)`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
)dnl
  [label local-async-static-call] .


--- remote-async-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Lcnt: F > CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), L) | SL }, PrQ: W, Lcnt: F > CLOCK
  invoc(O, EVAL(E, (S :: L), T), label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), Q, EVALLIST(EL, (S :: L), T))'
,dnl
`rl
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { insert(A, label(O, F), L) | SL }, PrQ: W, Lcnt: (F + 1) > CLOCK
  invoc(O, EVAL(E, (S :: L), T), label(O, F), Q , EVALLIST(EL, (S :: L), T)) '
)dnl
  [label remote-async-call] .


STEP(`< O : C | Att: S, Pr: { L | multicast(E ; Q ; EL) ; SL }, PrQ: W,
            Lcnt: F > CLOCK',
`< O : C | Att: S, Pr: { L | $multicast(EVAL(E, (S :: L), T) ; Q ; EVALLIST(EL, (S :: L), T)) ; SL }, PrQ: W,
            Lcnt: F > CLOCK',
`[label multicast-eval]')

eq 
  < O : C | Att: S, Pr: { L | $multicast(list(emp) ; Q ; DL) ; SL }, PrQ: W,
            Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >
  [label multicast-emit-list-emp] .

ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | $multicast(list('O'` :: DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(list(DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  invoc(O, 'O'`, label(O, 'O'`, Q, DL2), Q, DL2)',
`eq
  < O : C | Att: S, Pr: { L | $multicast(list('O'` :: DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(list(DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: (F + 1) >
  invoc(O, O''`, label(O, F), Q , DL2)')
  [label multicast-emit-list] .

eq 
  < O : C | Att: S, Pr: { L | $multicast(set(emptyset) ; Q ; DL); SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >
  [label multicast-emit-set-emp] .

ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | $multicast(set('O'` : DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(set(DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  invoc(O, 'O'`, label(O, 'O'`, Q, DL2), Q, DL2)',
`eq
  < O : C | Att: S, Pr: { L | $multicast(set('O'` : DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(set(DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: (F + 1) >
  invoc(O,' O'`, label(O, F), Q , DL2)')
  [label multicast-emit-set] .

--- return
---
STEP(`< O : C |  Att: S, Pr: { L | return(EL); SL }, PrQ: W, Lcnt: F > CLOCK',
`< O : C |  Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F > CLOCK
  comp(L[".label"], EVALLIST(EL, (S :: L), T))',
`[label return]')


--- transport
---
--- Receive an invocation message to bind the method body.
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Lcnt: F >
  invoc(O', O, N, Q, DL)
  =
  < O : C | Att: S, Pr: P, PrQ: W, Lcnt: F >
  bindMtd(O, O', N, Q, DL, C < emp >)
  [label transport-imsg] .

--- free
---
--- Free a label.  Make sure that the use of labels is linear.
---
STEP(< O : C | Att: S`,' Pr: { L | free(A) ; SL }`,' PrQ: W`,' Lcnt: F >,
  < O : C | Att: S`,' Pr: { insert(A`,' null`,' L) | SL }`,' PrQ: W`,'
            Lcnt: F >
  discard(L[A]),
  `[label free]')


--- deallocate
---
eq
  comp(N, DL) discard(N) = none [label deallocate] .


--- TAIL CALLS
---
--- Fake the caller and the label and tag the label.  Since we do not
--- want to interleave, this can also be an equation.
---
STEP(`< O : C | Att: S, Pr: { L | tailcall(E ; Q ; EL) ; SL }, PrQ: W,
            Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >
  invoc(O, EVAL(E, (S :: L), T), L[".label"], Q, EVALLIST(EL, (S :: L), T))'
  CLOCK,
`[label tailcall]')

--- STATIC TAIL CALLS
---
--- Fake the caller and the label and tag the label.  Since we do not
--- want to interleave, this can also be an equation.
---
STEP(`< O : C | Att: S, Pr: { L | statictail(Q ; "" ; "" ; EL) ; SL }, PrQ: W, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept tag(L[".label"])  }, PrQ: W, Lcnt: F >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), C < emp >)'
  CLOCK,
`[label local-tailcall]')

STEP(`< O : C | Att: S, Pr: { L | statictail(Q ; CC ; "" ; EL) ; SL }, PrQ: W, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept tag(L[".label"]) }, PrQ: W, Lcnt: F >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), CC < emp >)'
  CLOCK,
`[label static-tailcall]')

*** If we receive the method body, the call is accepted and the label untagged.
crl
  < O : C | Att: S, Pr: { noSubst | $accept N }, PrQ: W , { L | SL },
         Lcnt: F >
  =>
  < O : C | Att: S, Pr: { insert(".label", tag(N), L) | SL }, PrQ: W,
            Lcnt: F >
  if L[".label"] = N
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
< O : C | Att: S`,'Pr: { L | new (A ; CC ; EL); SL }`,' PrQ: W`,' Lcnt: F > 
  < CC : Class | Inh: I `,' Param: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: G >
  CLOCK`'dnl
,dnl
< O : C | Att: S`,' Pr: { L | assign(A ; newId(CC`,' G)); SL }`,' PrQ: W`,' Lcnt: F >
  < CC : Class | Inh: I `,' Param: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: (G + 1) >
  < newId(CC`,'G) : CC | Att: S`,' Pr: idle`,' PrQ: noProc`,' Lcnt: 0 >
  findAttr(newId(CC`,' G)`,' I`,' S'`,' 
    $assign(AL ; EVALLIST(EL, compose(S`,'  L), T))`,'
    { noSubst | call(".anon" ; "this" ; "init" ; emp) ; get(".anon" ; noVid) ;
    call (".anon" ; "this" ; "run" ; emp) ; free(".anon")}) CLOCK,dnl
`[label new-object]')


--- ATTRIBUTE inheritance with multiple inheritance
--- CMC assumes that all attributes names are (globally) different.
--- For the purpose of the CMC the class parameters are treated as
--- attributes!
---
op findAttr  : Oid InhList Subst StmtList Process -> Msg [ctor `format' (n d)] .
op foundAttr : Oid Subst  StmtList Process -> Msg [ctor `format' (n d)] .

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
  < C : Class | Inh: I, Param: AL, Att: S', Mtds: MS, Ocnt: G >
  =
  findAttr(O, (I' , I), compose(S', S),
           SL ; assign(AL ; EL), 
           { L' | static(".init" ; "init" ; C ; "" ; emp) ; get(".init" ; noVid) ; SL1 })
  < C : Class | Inh: I, Param: AL, Att: S', Mtds: MS, Ocnt: G > .

eq
  foundAttr(O, S', SL, { L' | SL1 })
  < O : C | Att: S, Pr: idle, PrQ: W, Lcnt: F >
  =
  < O : C | Att: ("this" |-> O, S'), Pr: { L' | SL ; SL1 }, PrQ: W, Lcnt: F > .



--- assert
---
STEP(dnl
`{ < O : C | Att: S, Pr: { L | assert(E) ; SL }, PrQ: W, Lcnt: F > CN CLOCK }',
`{ if EVALGUARD(E, (S :: L), CN, T) asBool then
    < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >
  else
    < O : C | Att: S, Pr: { L | failure(E) ; SL }, PrQ: W, Lcnt: F >
  fi CN CLOCK }',
`[label assert]')



--- REAL-TIME CREOL
---
--- posit
---
ifdef(`TIME',dnl
`CSTEP(
`{ < O : C | Att: S, Pr: { L | posit E ; SL }, PrQ: W, Lcnt: F > CN CLOCK }',
`{ < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F > CN CLOCK }',
EVALGUARD(E, (S :: L), CN, T) asBool,
`[label posit]')',
`STEP(
`< O : C | Att: S, Pr: { L | posit E ; SL }, PrQ: W, Lcnt: F >',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >',
`[label posit]')'dnl
)dnl END if time.


ifdef(`TIME',dnl
--- The following formalises the tick rule for real-time Creol.  This rule
--- is only enabled if and only if all posit constraints are satisfied in
--- the global state at the new time.

op posit(_,_,_) : Subst StmtList Float -> Bool .
eq posit(S, posit E ; SL, T) = EVAL(E, S, T) asBool .
eq posit(S, (SL1 [] SL2); SL, T) = posit(S, SL1, T) or posit(S, SL2, T) .
eq posit(S, (SL1 ||| SL2); SL, T) = posit(S, SL1, T) or posit(S, SL2, T) .
eq posit(S, SL, T) = true [owise] .

op posit(_,_,_) : Subst MProc Float -> Bool .
eq posit(S, (W , idle), T) = posit(S, W, T) .
eq posit(S, (W , { L | SL}), T) = posit((S :: L), SL, T) and posit(S, W, T) .
eq posit(S, noProc, T) = true .

op posit : Configuration Float -> Bool .
eq posit (c:Class CN, T) = posit (CN, T) .
eq posit (< O : C | Att: S, Pr: P, PrQ: W, Lcnt: F > CN, T) =
    posit (S, (W , P), T) and posit (CN, T) .
eq posit (none, T) = true .

*** A very simple discrete time clock.
crl
  { CN < T : Clock | delta: delta > }
  =>
  { CN < T + delta : Clock | delta: delta >  }
  if posit (CN, T + delta)
  [label tick] .
)dnl

endm
