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
*** Creol's state configuration.
***
*** Modeled after the CONFIGURATION module in "prelude.maude"
***
mod CREOL-CONFIGURATION is

    protecting CREOL-DATA-LABEL .
    protecting CREOL-PROCESS-POOL .
changequote(`[[[[', `]]]]')dnl
    protecting LIST{Inh} * (sort List{Inh} to InhList,
			    sort NeList{Inh} to NeInhList,
			    op nil : -> List{Inh} to noInh,
			    op __ : List{Inh} List{Inh} -> List{Inh} to _`,`,_) .
    protecting SET{Method} * (sort Set{Method} to MMtd,
			      op empty : -> Set{Method} to noMethod,
                              op _`,_ : Set{Method} Set{Method} -> Set{Method} to _*_ [[[[[format]]]] (d r o d)] ) .
changequote dnl

    --- The standard configuration of Maude.
    protecting CONFIGURATION .

    subsort Oid < Data .

    --- Define object identifiers.
    protecting CONVERSION .

    sorts Body Invoc Comp .
    subsorts Invoc Comp < Body .

    op ob : String -> Oid [ctor `format' (r o)] .

    var C : String .
    var N : Nat .

    --- Create a new fresh name for an object.
    op newId : String Nat -> Oid .
    eq newId(C, N)  = ob(C + string(N,10)) .

    --- INVOCATION and REPLY
    op invoc : Oid Label String DataList -> Invoc [ctor `format'(b o)] .  
    op comp : Label DataList -> Comp [ctor `format' (b o)] .  

    --- Messages.  Messages have at least a receiver.

    --- Invocation and completion message.
    op _from_to_ : Body Oid Oid -> Msg [ctor `format' (o ! o ! o on)] .

    --- Error and warning messages are intended to stop the machine.
    --- For now, nothing is emitting these.
    --- op error(_) : String -> [Msg] [ctor `format' (nnr r o! or onn)] .
    op warning(_) : String -> [Msg] [ctor `format' (nnr! r! r! or onn)] .

    sort MMsg .
    subsort Body < MMsg .

    op noMsg : -> MMsg [ctor] .
    op _+_ : MMsg MMsg -> MMsg [ctor assoc comm id: noMsg] . 


    --- Define class declarations as an object.
    ---
    op Class : -> Cid [ctor `format' (c o)] .
    op cl : String -> Oid [ctor `format' (c o)] .
    op Inh:_ : InhList -> Attribute [ctor] .
    op Par:_ : VidList -> Attribute [ctor] .
    op Att:_ : Subst -> Attribute [ctor] .
    op Mtds:_ : MMtd -> Attribute [ctor] .
    op Ocnt:_ : Nat -> Attribute [ctor] .

    --- Terms of sort Object represent objects (and classes) in the
    --- run-time configuration.
    ---
    --- Terms of sort Cid represent class names.
    subsort String < Cid .
    op noObj : -> Object [ctor] .

    op Pr:_ : Process -> Attribute [ctor] .
    op PrQ:_ : MProc -> Attribute [ctor] .
    op Ev:_ : MMsg -> Attribute [ctor] .
    op Lcnt:_ : Nat -> Attribute [ctor] .

ifdef(`TIME',dnl
    sort Clock .
    subsort Clock < Configuration .

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



    --- System initialisation
    var DL : DataList .
    op main : String DataList -> Configuration .
    eq main(C,DL) =
      < ob("main") : "" | Att: noSubst, 
        Pr: ("var" |-> null, ("var" ::= new C(DL))), PrQ: noProc,
        Ev: noMsg, Lcnt: 0 > .

endm
