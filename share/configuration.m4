dnl
dnl configuration.m4 -- The specification of state configurations, compatible
dnl with Maude's configuration module.
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
			    op __ : List{Inh} List{Inh} -> List{Inh} to _`,_) .
    protecting SET{Method} * (sort Set{Method} to MMtd,
			      op empty : -> Set{Method} to noMethod) .
changequote dnl

    --- Define object identifiers.
    protecting CONVERSION .

    sorts Oid Cid Msg Class ifdef(`TIME', `Clock ')Object Configuration .
    subsort Oid < Data .
    subsorts Class ifdef(`TIME', `Clock ')Msg Object < Configuration .

    op ob(_) : String -> Oid [ctor `format' (d d ! o d)] .

    vars C M M' : String .
    vars O O' : Oid .
    var S : Subst .
    vars I I' : InhList .
    vars P P' : Process .
    vars W : MProc .
    var MS : MMtd .
    var AL : VidList .
    var SL : StmtList .
    var EL : ExprList .
    var DL : DataList .
    var N : Label .
    var F : Nat .

    --- Create a new fresh name for an object.
    op newId : String Nat -> Oid .
    eq newId(C, F)  = ob(C + string(F,10)) .

    --- Invocation message.
    ---
    --- invoc(S,R,N,M,DL)
    --- S: The sender.
    --- R: The receiver.
    --- N: The label.
    --- M: The called method.
    --- DL: The actual arguments.
    op invoc(_,_,_,_,_) : Oid Oid Label String DataList -> Msg
      [ctor `format' (b d o  b so  b so  b so  b so b on)] .

    --- Completion message.
    ---
    --- comp(N,DL)
    --- N: The label
    --- DL: The result values.
    op comp(_,_) : Label DataList -> Msg
      [ctor `format' (b d o  b so  b on)] .

    --- Instruct the runtime system to drop the message.
    op discard(_) : Label -> Msg [ctor `format' (b d o b on)].

    --- Error and warning messages are intended to stop the machine.
    --- For now, nothing is emitting these.
    --- op error(_) : String -> [Msg] [ctor `format' (nnr r o! or onn)] .
    op warning(_) : String -> [Msg] [ctor `format' (nnr! r! r! or onn)] .


    --- Fetch pair { code |  vars } to bind call to process.
    ---
    --- M   represents the name of the method.
    --- C   represents the name of the class.
    --- MS  represents the methods we search through.
    --- O   represents the identity of the caller.
    --- N   represents the label used to return the value computed by the
    ---     method.
    --- DL  represents the list of actual arguments.
    op get : String String MMtd Oid Label DataList -> Process .

    eq get(M, C, (MS, < M : Method | Param: AL, Att: S, Code: SL >), O, N, DL) =
        { "caller" |-> O, ".class" |-> str(C), ".label" |-> N,
          ".method" |-> str(M), S | assign(AL ; DL) ; SL } .
    eq get(M, C, MS, O, N, DL) = notFound [owise] .


    --- Terms of sort Object represent objects (and classes) in the
    --- run-time configuration.
    ---
    --- Terms of sort Cid represent class names.
    subsort String < Cid .

    --- This term is the class name of "class objects."
    op Class : -> Cid [ctor `format' (c o)] .

    op noObj : -> Object [ctor] .
    op <_:_ | Att:_, Pr:_, PrQ:_, Lcnt:_> : 
       Oid String Subst Process MProc Nat -> Object 
         [ctor `format' (nr d d g ++r nir o  r ni o  r ni o  r ni o--  r on)] .


    --- Define Classes.
    --- Class declaration.
    ---
    op <_: Class | Inh:_, Param:_, Att:_, Mtds:_, Ocnt:_> : 
      String InhList VidList Subst MMtd Nat -> Class 
       [ctor `format' (ng ! og o d  sg o d  sg o d  sg o d  sg++ oni o  gni o-- g on)] .


    --- Method binding messages.
    --- Bind method request
    --- Given: caller callee label method params (list of classes to look in)
    op bindMtd : Oid Oid Label String DataList InhList -> Msg
        [`format'(!r d)] .

    --- Successfully bound method body. 
    --- Consider the call O.Q(I). bindMtd(O,Q,I,C S) tries to find Q in
    --- class C or superclasses, then in S. boundMtd(O,Mt) is the result.
    op boundMtd : Oid Process -> Msg [`format'(!r d)] .

    --- Method binding with multiple inheritance
    ---
    eq
      bindMtd(O, O', N, M, DL, (C < EL > , I'))
      < C : Class | Inh: I , Param: AL, Att: S , Mtds: MS , Ocnt: F >
      =
      if get(M, C, MS, O', N, DL) == notFound then
        bindMtd(O, O', N, M, DL, (I , I'))
      else
        boundMtd(O, get(M, C, MS, O', N, DL))
      fi
      < C : Class | Inh: I , Param: AL, Att: S , Mtds: MS , Ocnt: F > .

    eq
      boundMtd(O, P')
      < O : C | Att: S, Pr: P, PrQ: W, Lcnt: F >
      =
      < O : C | Att: S, Pr: P, PrQ: (W , P'), Lcnt: F > .


    --- Define a configuration
    op none : -> Configuration [ctor] .
    op __ : Configuration Configuration -> Configuration
	  [ctor assoc comm id: none] .

ifdef(`TIME',dnl
  *** Definition of a global clock in the system
  op < clock : Clock | Value:_`,' Delta:_ > : Float Float -> Clock
    [ctor ``format'' (c o c c c c o c o)] .
)dnl

  *** Useful for real-time maude and some other tricks.
ifdef(`MODELCHECK',dnl
  *** Maude's model checker asks us to provide State.
  including SATISFACTION .
  including MODEL-CHECKER .

,dnl
  *** We should not provide sort State`,' since this is used in LOOP-MODE.
  *** For now`,' we do.
  sort State .
)dnl

  op {_} : Configuration -> State [ctor] .


    var MG : Msg .
    var CL : Class .
    var OB : Object .
    var CN : Configuration .

    --- System initialisation
    op main : Configuration String DataList -> State .
    eq main(CN, C, DL) =
      { CN < ob("main") : "" | Att: noSubst, 
             Pr: { "var" |-> null | new("var" ; C ; DL) }, PrQ: noProc,
             Lcnt: 0 > } .

    op allMessages : Configuration -> Configuration .
    eq allMessages(none) = none .
    eq allMessages(MG CN) = MG allMessages(CN) .
    eq allMessages(CL CN) = allMessages(CN) .
    eq allMessages(OB CN) = allMessages(CN) .

endm
