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
    protecting CREOL-CID .
    protecting CREOL-OID .
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

    sorts Msg Class ifdef(`TIME', `Clock ')Object Configuration .
    subsorts Class ifdef(`TIME', `Clock ')Msg Object < Configuration .

    vars B M M' : String .
    var C : Cid .
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
ifdef(`WITH_UPDATE',
`    vars T T1 V : Nat .
    var B1 : String .
    var CL : Class .
    var OB : Object .
    var MSG : Msg .
ifdef(`TIME',
`    var CLOCK : Clock .
')dnl
')dnl

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
    op get : String Cid MMtd Oid Label DataList -> Process .

    eq get(M, CLASS(B, F), (MS, < M : Method | Param: AL, Att: S, Code: SL >), O, N, DL) =
        { "caller" |-> O, ".class" |-> str(B), ifdef(`WITH_UPDATE', `".stage" |-> int(F), ')
          ".label" |-> N, ".method" |-> str(M), S | assign(AL ; DL) ; SL } .
    eq get(M, C, MS, O, N, DL) = notFound [owise] .


    --- Terms of sort Object represent objects (and classes) in the
    --- run-time configuration.
    ---

    op noObj : -> Object [ctor] .
    op <_:_ | Att:_, Pr:_, PrQ:_, Lcnt:_> : 
       Oid Cid Subst Process MProc Nat -> Object 
         [ctor `format' (nr d d g ++r nir o  r ni o  r ni o  r ni o--  r on)] .


ifdef(`WITH_UPDATE',
  `define(`VERSION', `Version: $1, ')',
  `define(`VERSION', `')')dnl
    --- Define Classes.
    --- Class declaration.
    ---
ifdef(`WITH_UPDATE',
`    op <_: Class | Version:_, Inh:_, Param:_, Att:_, Mtds:_, Ocnt:_> : 
      Cid Nat InhList VidList Subst MMtd Nat -> Class 
       [ctor `format' (ng ! og o d  sg o d  sg o d  sg o d  sg o d  sg++ oni o  gni o-- g on)] .',
`    op <_: Class | Inh:_, Param:_, Att:_, Mtds:_, Ocnt:_> : 
      Cid InhList VidList Subst MMtd Nat -> Class 
       [ctor `format' (ng ! og o d  sg o d  sg o d  sg o d  sg++ oni o  gni o-- g on)] .')


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
      < C : Class | VERSION(V)Inh: I , Param: AL, Att: S , Mtds: MS , Ocnt: F >
      =
      if get(M, C, MS, O', N, DL) == notFound then
        bindMtd(O, O', N, M, DL, (I , I'))
      else
        boundMtd(O, get(M, C, MS, O', N, DL))
      fi
      < C : Class | VERSION(V)Inh: I , Param: AL, Att: S , Mtds: MS , Ocnt: F > .

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

ifdef(`WITH_UPDATE',
`    sorts ClassDep ClassDeps ObjectDep ObjectDeps .

    subsorts ClassDep < ClassDeps .
    op none : -> ClassDeps [ctor] .
    op _,_ : ClassDeps ClassDeps -> ClassDeps [ctor assoc comm id: none] .
    op c(_,_) : String Nat -> ClassDep .

    subsorts ObjectDep < ObjectDeps .
    op none : -> ObjectDeps [ctor] .
    op _,_ : ObjectDeps ObjectDeps -> ObjectDeps [ctor assoc comm id: none] .
    op o(_,_) : Oid Nat -> ObjectDep .
    
    --- Add a new class into the system.
    op add(_,_) : Class ClassDeps -> Msg 
      [ctor format (b d o  b so  b on)] .

    --- Extend an existing class.
    op extend(_,_,_,_,_,_) : String InhList Subst MMtd StmtList ClassDeps -> Msg
      [ctor format (b d o  b so  b so  b so  b so  b so  b on)] .

    --- Simplify a class.
    op remove(_,_,_,_,_,_) : String InhList Subst MMtd ClassDeps ObjectDeps
      -> Msg [ctor format (b d o  b so  b so  b so  b so  b so  b on)] .

    --- Transfer updates class state to object state.
    op transfer(_,_,_,_) : Oid Subst InhList StmtList
      -> Msg [ctor format (b d o  b so  b so  b so  b on)] .

    op allinstances : String Nat Configuration -> ObjectDeps .
    eq allinstances(B, T, CL CN) = allinstances(B, T, CN) .
    eq allinstances(B, T, MSG CN) = allinstances(B, T, CN) .
ifdef(`WITH_TIME', `    eq allinstances(B, T, CLOCK CN) = allinstances(B, T, CN) .
')dnl
    eq allinstances(B, T, < O : class(B1, T1) | Att: S, Pr: P, PrQ: W, Lcnt: F > CN) =
        if B == B1 then
            allinstances(B, T, CN), o(O, T)
        else
            allinstances(B, T, CN)
        fi .
    eq allinstances(B, T, none) = none .

    op update : Nat Nat MMtd -> StmtList .
    ceq update(T, T1, MS) = noStmt if T >= T1 .
    eq update(T, T1, (< ".update" : Method | Param: noVid, Att: ".version" |-> int(T), Code: SL >, MS)) =
          SL ; update(s T, T1, MS) [owise] .'
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

ifdef(`LOGGING',dnl
    sort evalState .
    vars trans inits : TSubst .

    op { _ | _ | _ }    : StmtList TSubst TSubst -> evalState [ctor] .
    op _[stmts] : evalState -> StmtList .
    op _[trans] : evalState -> TSubst .
    op _[init] : evalState -> TSubst .
    eq { SL | trans | inits }[stmts] = SL .
    eq { SL | trans | inits }[trans] = trans .
    eq { SL | trans | inits }[init] = inits .

--- Log object`,' Cnt is the index of the snapshot
    op <log From: _ To: _ Type: _ Data: _ Att: _ Label: _ > : Nat Nat String evalState Subst String -> Object [format (ng! o d d d d b! onssss d d d d r! d no) ] .
    op <choice Number: _ Type: _ Expression: _ > : Nat String Expr -> Object [format (ng! o b! o b! o o o no) ] .
,)dnl
  var CN : Configuration .

  --- System initialisation
  op main : Configuration String DataList -> State .
  eq main(CN, B, DL) =
    { CN < ob("main") : Start | Att: noSubst, 
           Pr: { "var" |-> null | new("var" ; CLASS(B, 0) ; DL) }, PrQ: noProc,
           Lcnt: 0 > ifdef(`LOGGING',`
'      < ob("log") : "" | Att: noSubst`,' Pr: idle`,' PrQ: noProc`,' Lcnt: 0 > 
      <log From: 0 To: 0 Type: "lastrun" Data: { skip | TnoSubst | TnoSubst } Att: noSubst Label: "lastrun" > 
)} .

endm
