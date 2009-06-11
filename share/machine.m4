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

  vars F G : Nat .                     --- Counters for generating fresh names
  vars O O1 : Oid .                    --- Object identifiers
  vars C CC : Cid .                    --- Class names
  var Q : String .                     --- Generic names (attribute and method)
  var A : Vid .                        --- Generic attribute names
  var AL : VidList .                   --- List of LHS
  var N : Label .                      --- Call label
  var D : Data .                       --- Value
  vars DL DL2 : DataList .             --- List of values
  vars DS : DataSet .		       --- Set of data items
  var E : Expr .                       --- Expression
  var EL : ExprList .                  --- List of Expressions
  var ST : Stmt .                      --- Statement
  var SST : SuspStmt .                 --- Suspendable statement
  vars S S1 L L1 : Subst .             --- Object and process states
  vars SL SL1 SL2 : StmtList .         --- List of statements
  var P : Process .
  var W : MProc .
  vars I I1 : InhList .
  var MS : MMtd .
  var CN : Configuration .
  var CO : Bool .                      --- Whether a future completed.
ifdef(`WITH_UPDATE',
`  var V V1 T T1 T2 : Nat .                --- Class and object versions
  var G1 : Nat .
  var B B1 : String .                  --- Class name
  var CL : Class .                     --- A class
  var I2 : InhList .
  var AL1 : VidList .
  var MS1 : MMtd .                     --- Methods to add to a class
  var CD : ClassDeps .
  var OD : ObjectDeps .',
`  var B : Cid .')

dnl Define the clock and the variables needed to address clocks.
dnl
dnl If WITH_TIME is not defined, CLOCK will be defined to empty.
ifdef(`WITH_TIME',
  vars delta T : Float .
`define(`CLOCK', `< T : Clock | delta: delta >')',dnl
`define(`CLOCK', `')')dnl

ifdef(`MODELCHECK',dnl
  op label : Oid Oid String DataList -> Label [ctor ``format'' (! o)] .
  eq caller(label(O, O1, Q, DL)) = O . 
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
  < O : C | Att: S, Pr: { L | $assign((Q @ B), AL ; D :: DL) ; SL },
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
`< O : C | Att: S, Pr: { L | if E th SL1 el SL2 fi ; SL }, PrQ: W, Lcnt: F >
  CLOCK',
`if EVAL(E, (S :: L), T) asBool then
    < O : C | Att: S, Pr: { L | SL1 ; SL }, PrQ: W, Lcnt: F >
  else
    < O : C | Att: S, Pr: { L | SL2 ; SL }, PrQ: W, Lcnt: F >
  fi
  CLOCK',
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
  < N : Future | Completed: true, References: G, Value: DL >
  =>
  < O : C |  Att: S, Pr: { L | assign(AL ; DL) ; SL }, PrQ: W, Lcnt: F >
  < N : Future | Completed: true, References: G, Value: DL >
  [label receive-comp] .


--- local-reply
---
CSTEP(dnl
`< O : C | Att: S, Pr: { L | get(N ; AL) ; SL }, PrQ: W , { L1 | SL1 }, Lcnt: F >',
`< O : C | Att: S, Pr:  { L1 | SL1 ; $cont N },
  PrQ: W , { L | get(N ; AL) ; SL }, Lcnt: F >',
`L1[".label"] == N',
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
  < O : C | Att: S, Pr: { L | $cont N }, PrQ: W , { L1 | get(N ; AL) ; SL1},
    Lcnt: F >
  =>
  < O : C | Att: S, Pr: { L1 | get(N ; AL) ; SL1 }, PrQ: W,
    Lcnt: F >
  [label continue] .


--- local-async-static-call
---
ifdef(`MODELCHECK',
`ceq
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; None ; EL ); SL }, PrQ: W, Lcnt: F >
  CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, N, L) | SL }, PrQ: W, Lcnt: F >
  < N : Future | Completed: false, References: 1, Value: emp >
  bindMtd(O, O, N, Q, EVALLIST(EL, (S :: L), T), CC < emp >) CLOCK
  if N := label(O, O, Q, EVALLIST(EL, (S :: L), T))'
,
`crl
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; None ; EL ); SL }, PrQ: W, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { insert (A, N, L) | SL }, PrQ: W, Lcnt: (s F) >
  < N : Future | Completed: false, References: 1, Value: emp >
  bindMtd(O, O, N, Q, EVALLIST(EL, (S :: L), T), CC < emp >) CLOCK
  if N := label(O, F)'
)dnl
  [label local-async-static-call] .


--- remote-async-call
---
ifdef(`MODELCHECK',
`ceq
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Lcnt: F > CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, N, L) | SL }, PrQ: W, Lcnt: F > CLOCK
  invoc(O, O1, N, Q, DL)
  if DL := EVALLIST(EL, (S :: L), T)
  /\ O1 := EVAL(E, (S :: L), T)
  /\ N := label(O, O1, Q, DL)
  /\ O =/= O1'
,dnl
`crl
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { insert(A, N, L) | SL }, PrQ: W, Lcnt: (s F) > CLOCK
  invoc(O, O1, N, Q , DL)
  if DL :=  EVALLIST(EL, (S :: L), T)
  /\ O1 := EVAL(E, (S :: L), T)
  /\ N := label(O, F)
  /\ O =/= O1'
)dnl
  [label remote-async-call] .

--- remote-async-self-call
---
ifdef(`MODELCHECK',
`ceq
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Lcnt: F > CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, N, L) | SL }, PrQ: W, Lcnt: F > CLOCK
  invoc(O, O, N, Q, EVALLIST(EL, (S :: L), T))
  if N := label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)) /\
     O = EVAL(E, (S :: L), T)'
,dnl
`crl
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { insert(A, N, L) | SL }, PrQ: W, Lcnt: (s F) > CLOCK
  invoc(O, O, N, Q , EVALLIST(EL, (S :: L), T))
  if N := label(O, F) /\ O = EVAL(E, (S :: L), T)'
)dnl
  [label remote-async-self-call] .



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
  < O : C | Att: S, Pr: { L | $multicast(list('O1` :: DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(list(DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  invoc(O, O1, label(O, O1, Q, DL2), Q, DL2)',
`eq
  < O : C | Att: S, Pr: { L | $multicast(list('O1` :: DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(list(DL) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: (s F) >
  invoc(O, O1, label(O, F), Q , DL2)')
  [label multicast-emit-list] .

eq 
  < O : C | Att: S, Pr: { L | $multicast(set(emptyset) ; Q ; DL); SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F >
  [label multicast-emit-set-emp] .

ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | $multicast(set('O1` : DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(set(DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  invoc(O, O1, label(O, O1, Q, DL2), Q, DL2)',
`eq
  < O : C | Att: S, Pr: { L | $multicast(set('O1` : DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(set(DS) ; Q ; DL2) ; SL },
            PrQ: W, Lcnt: (s F) >
  invoc(O, O1, label(O, F), Q , DL2)')
  [label multicast-emit-set] .

--- return
---
CSTEP(`< O : C |  Att: S, Pr: { L | return(EL); SL }, PrQ: W, Lcnt: F > CLOCK
  < N : Future | Completed: false, References: G, Value: emp >',
`< O : C |  Att: S, Pr: { L | SL }, PrQ: W, Lcnt: F > CLOCK
  < N : Future | Completed: true, References: G, Value: EVALLIST(EL, (S :: L), T) >',
`N == L[".label"]',
`[label return]')


--- transport
---
--- Receive an invocation message to bind the method body.
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Lcnt: F >
  invoc(O1, O, N, Q, DL)
  =
  < O : C | Att: S, Pr: P, PrQ: W, Lcnt: F >
  < N : Future | Completed: false, References: 1, Value: emp >
  bindMtd(O, O1, N, Q, DL, C < emp >)
  [label transport-imsg] .

--- free
---
--- Free a label.  Make sure that the use of labels is linear.
---
--- sd(G,1) works, because G is always positive. Maude does not have
--- a nice decrement operator.
CSTEP(`< O : C | Att: S, Pr: { L | free(A) ; SL }, PrQ: W, Lcnt: F >
  < N : Future | Completed: CO, References: G, Value: DL >',
`< O : C | Att: S, Pr: { insert(A, null, L) | SL }, PrQ: W, Lcnt: F >
  < N : Future | Completed: CO, References: sd(G, 1), Value: DL >',
`N = L[A]',
  `[label free]')


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
STEP(`< O : C | Att: S, Pr: { L | statictail(Q ; None ; None ; EL) ; SL }, PrQ: W, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept tag(L[".label"])  }, PrQ: W, Lcnt: F >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), C < emp >)'
  CLOCK,
`[label local-tailcall]')

STEP(`< O : C | Att: S, Pr: { L | statictail(Q ; CC ; None ; EL) ; SL }, PrQ: W, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept tag(L[".label"]) }, PrQ: W, Lcnt: F >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), CC < emp >)' CLOCK,
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
--- The new object will receive its initial attributes from the foundAttr
--- message below and will not have attributes before that.
---
STEP(dnl
`< O : C | Att: S, Pr: { L | new(A ; B ; EL); SL }, PrQ: W, Lcnt: F >
  < CLASS(B, T) : Class | VERSION(V)Inh: I , Param: AL, Att: S1, Mtds: MS, Ocnt: G >
  CLOCK'dnl
,dnl
`< O : C | Att: S, Pr: { L | assign(A ; newId(B, G)); SL }, PrQ: W, Lcnt: (s F) >
  <  CLASS(B, T) : Class | VERSION(V)Inh: I, Param: AL, Att: S1, Mtds: MS, Ocnt: (s G) >
  < newId(B, G) :  CLASS(B, T) | Att: noSubst, Pr: idle, PrQ: noProc, Lcnt: 0 >
  findAttr(newId(B`,' G), I, S1, 
    $assign(AL ; EVALLIST(EL, compose(S,  L), T)),
    { ifdef(`MODELCHECK', `noSubst', `".label" |-> label(O, F)') |
        call(".anon" ; "this" ; "init" ; emp) ;
        get(".anon" ; noVid) ;
        free(".anon") ;
        call (".anon" ; "this" ; "run" ; emp) ;
        free(".anon") }) CLOCK',dnl
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
  findAttr(O,(C < EL > , I1), S, SL, { L1 | SL1 }) 
  < C : Class | VERSION(V)Inh: I, Param: AL, Att: S1, Mtds: MS, Ocnt: G >
  =
  findAttr(O, (I1 , I), compose(S1, S),
           SL ; assign(AL ; EL), 
           { L1 | static(".init" ; "init" ; C ; None ; emp) ;
                  get(".init" ; noVid) ; free(".init") ; SL1 })
  < C : Class | VERSION(V)Inh: I, Param: AL, Att: S1, Mtds: MS, Ocnt: G > .

eq
  foundAttr(O, S1, SL, { L1 | SL1 })
  < O : C | Att: S, Pr: idle, PrQ: W, Lcnt: F >
  =
  < O : C | Att: ("this" |-> O, S1), Pr: { L1 | SL ; SL1 }, PrQ: W, Lcnt: F > .



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


ifdef(`WITH_UPDATE',dnl
--- The following rules implement the operational semantics of class
--- updates.
---
STEP(``add(< class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >, none)'',
``< class(B, (s T)) : Class | Version: (s V), Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >'',
`[label add-class]')

--- Extend a class. B is the name of the class we wany to upgrade.
--- A method .update is added that updates an object of class B#T to
--- an object of class B#(s T)
---
STEP(dnl
``extend(B, I1, S1, MS1, SL, none)
    < class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >'',
``< class(B, s T) : Class | Version: (s V), Inh: (I, I1), Param: AL, Att: (compose(S, S1)),
                          Mtds: MS1, remove(MS, MS1),
                          < ".update" : Method | Param: noVid,
                                                 Att: ".version" |-> int(T),
                                                 Code: SL >,
                            Ocnt: G >'',
`[label extend-class]')

--- When all the update constraints are resolved`,' we are allowed to
--- simplify class CC.
STEP(dnl
``remove(B, I, S, MS, none, none)
    < class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S1, Mtds: MS1, Ocnt: G >'',
``< class(B, s T) : Class | Version: (s V), Inh: I, Param: AL, Att: remove(S1, S), Mtds: remove(MS1, MS), Ocnt: G >'',
`[label simplify-class]')

--- Resolve dependencies
CSTEP(dnl
``add(CL, (c(B, V1), CD))
    < class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >'',
``add(CL, CD)
    < class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >'',
`V >= V1',
`[label depend-add]')

CSTEP(dnl
``extend(B, I1, S1, MS1, SL, (c(B1, V1), CD))
    < class(B1, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >'',
``extend(B, I1, S1, MS1, SL, CD)
    < class(B1, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >'',
`V >= V1',
`[label depend-extend]')

CSTEP(dnl
``{ remove(B1, I1, S1, MS1, (c(B, V1), CD), OD)
    < class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >
    CN }'',
``{ remove(B1, I1, S1, MS1, CD, (OD, allinstances(B, T, CN)))
    < class(B, T) : Class | Version: V, Inh: I, Param: AL, Att: S, Mtds: MS, Ocnt: G >
    CN }'',
`V >= V1',
`[label depend-remove]')

--- Resolve dependencies on the object level. This is only relevant for
--- simplification.
CSTEP(dnl
``remove(B1, I1, S1, MS, CD, (o(O, T1), OD))
    < O : class(B, T) | Att: S, Pr: P, PrQ: W, Lcnt: F >'',
``remove(B1, I1, S1, MS, CD, OD)
    < O : class(B, T) | Att: S, Pr: P, PrQ: W, Lcnt: F >'',
`T1 <= T',
`[label depend-object1]')

--- Update a sub class.
CSTEP(dnl
``< class(B, T) : Class | Version: V, Inh: (I, class(B1, T1) < EL >, I1),
                          Param: AL, Att: S, Mtds: MS, Ocnt: G >
    < class(B1, T2) : Class | Version: V1, Inh: I2,
                              Param: AL1, Att: S1, Mtds: MS1, Ocnt: G1 >'',
``< class(B, s T) : Class | Version: V, Inh: (I, class(B, T2) < EL >, I1),
                            Param: AL, Att: S, Mtds: MS, Ocnt: G >
    < class(B1, T2) : Class | Version: V1, Inh: I2,
                              Param: AL1, Att: S1, Mtds: MS1, Ocnt: G1 >'',
``T1 < T2'',
``[label update-sub]'')

--- Update the object state after a class update.
---
--- First step: emit the transfer message to update the object state.
---
CSTEP(``< O : class(B, T) | Att: S, Pr: idle, PrQ: W, Lcnt: F >
   < class(B, T1) : Class | Version: V, Inh: I , Param: AL, Att: S1, Mtds: MS, Ocnt: G >'',
``< O : class(B, T1) | Att: noSubst, Pr: idle, PrQ: W, Lcnt: F >
    < class(B, T1) : Class | Version: V, Inh: I , Param: AL, Att: S1, Mtds: MS, Ocnt: G >
    transfer(O, S, class(B, T1) < emp >, update(T, T1, MS))'',
``T1 > T'',
``[label update-object]'')

--- Second step: collect all the upgrades from classes. Do not care for
--- the class version`,' because all classes cannot change while the object
--- update rule triggers.
---
``eq transfer(O, S, (class(B, T) < EL >, I), SL)
   < class(B, T1) : Class | Version: V, Inh: I1, Param: AL, Att: S1, Mtds: MS, Ocnt: G >
  =
  transfer(O, compose(S1, S), (I, I1), SL)
   < class(B, T1) : Class | Version: V, Inh: I1, Param: AL, Att: S1, Mtds: MS, Ocnt: G > .''
  
--- Third step: once the transfer is complete`,' update the object's state.
``eq < O : class(B, T1) | Att: noSubst, Pr: idle, PrQ: W, Lcnt: F >
    transfer(O, S, noInh, SL)
  =
  < O : class(B, T1) | Att: S, Pr: { noSubst | SL }, PrQ: W, Lcnt: F > .''


)dnl
--- REAL-TIME CREOL
---
--- posit
---
ifdef(`WITH_TIME',dnl
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


ifdef(`WITH_TIME',dnl
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
