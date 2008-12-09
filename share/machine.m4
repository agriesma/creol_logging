dnl
dnl machine.m4 -- The specification of the machine.
dnl
dnl Copyright (c) 2007, 2008
dnl
dnl The purpose of this file is to create the files `interpreter.maude', 
dnl `logginginterpreter.maude' and `modelchecker.maude'.  These files 
dnl have to be processed with dnl m4, with either one of `CREOL', 
dnl `LOGGING' or `MODELCHECK' defined.
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
dnl

ifdef(`LOGGING', dnl
`define(`PRELOG', `< ob("log") : "" | Att: noSubst`,' Pr: idle`,' PrQ: noProc`,' Dealloc: noDealloc`,' Ev: noMsg`,' Lcnt: logcnt >
  ')define(`POSTLOG', `< ob("log") : "" | Att: noSubst`,' Pr: idle`,' PrQ: noProc`,' Dealloc: noDealloc`,' Ev: noMsg`,' Lcnt: logcnt + 1 >
dnl <log From: logcnt To: ( logcnt + 1 ) Type: $2 Data: { $1 | $3 | $4 }  Att: ( S, L )  Label: getLabel((L,S)) > 
  <log From: logcnt To: ( logcnt + 1 ) Type: $2 Data: { $1 | $3 | $4 }  Att: noSubst  Label: getLabel((L,S)) > 
  ')
define(`MARKER', `$marker( $1 ) ; ')
define(`RMARKER', `$rmarker( $1 , $2 ) ; ')',dnl
`define(`PRELOG', `')'
`define(`POSTLOG', `')' 
`define(`MARKER', `')'
`define(`RMARKER', `')' )dnl

ifdef(`MODELCHECK',dnl
  op label : Oid Oid String DataList -> Label [ctor ``format'' (! o)] .
  eq caller(label(O, O', Q, DL)) = O . 
,dnl
 op label : Oid Nat -> Label [ctor ``format'' (o o)] .
 eq caller(label(O, F)) = O .
)dnl


ifdef(`LOGGING', dnl
vars E1 E2 E3 E4 : Expr .
vars V1 V2 : Vid .
vars D1 D2 : Data .
vars TS1 TS2 TS3 TS4 : TSubst .
var neEL : NeExprList .
var transstmt : Stmt .
vars ctrans cinits inits trans : TSubst .
var  CLabel : String .
var  CSL : StmtList .
var CS : Subst .
vars G1 G2 G3 F1 : Nat .

----------------------------------------------------------------------
--- helper functions for creating the log messages
----------------------------------------------------------------------
  var logcnt : Nat .
 op toString : Label -> String .
 eq toString( label(ob(C), F) ) = C + "-" + string(F, 10) .

 op toString : Oid -> String .
 eq toString(ob(C) ) = C .


 op getThis : Subst -> String .
 ceq getThis(S) = toString(S["this"]) if $hasMapping(S, "this") .
 eq getThis(S) = "global" [owise] .

 op getLabel : Subst -> String .
 ceq getLabel(S) = toString(S[".label"]) if $hasMapping(S, ".label") .
 ceq getLabel(S) = toString(S["this"]) if $hasMapping(S, "this") .
 eq getLabel(S) = "nolabel" [owise] .

---  delete an entry from a map
op delete : Vid TSubst -> TSubst .
eq delete(A , (TS1, A |> E1)) =
   if $hasMapping( TS1 , A) then delete(A, TS1)
   else TS1
   fi .

--- convert a Subst to TSubst
op toTrans : Subst -> TSubst .
eq toTrans(noSubst) = TnoSubst .
eq toTrans( ( V1 |-> E1, S) ) = insert( V1, E1, toTrans(S) ) .

--- combine assignment transitions
op getParamsR : TSubst Nat ExprList -> ExprList .
eq getParamsR( TnoSubst , F, EL) = EL .
eq getParamsR( TS1 , F , EL ) = getParamsR( ( delete(string(F, 10) , TS1) ) , (F + 1) , (EL :: (TS1[ string(F, 10) ])) ) .

op getParams : TSubst -> ExprList .
eq getParams( TS1 ) = getParamsR( TS1, 0, emp ) .

--- insertValues (TS1, TS2):  for each RHS in TS2`,' replace the variables by the expressions defined in TS1
--- EXAMPLE: rew insertValues(  ("y" |> "z" ) , ("x" |> "+" ("y" :: int(1) ) )) .
---          rew insertValues(  ("y" |> "z", "f" |> int(1) ) , ("x" |> "+" ("y" :: "f" ) )) .
--- TODO can this be put in an other function?
op insertValues : TSubst TSubst -> TSubst .
eq insertValues( TS1, TS2 ) = insertValuesR( TS1, TS2, TnoSubst) .

op insertValuesR : TSubst TSubst TSubst -> TSubst .  
eq insertValuesR( TS1, TnoSubst, TS3 ) = TS3 .
eq insertValuesR( TS1, (V2 |> E2, TS2), TS3 ) = insertValuesR( TS1, TS2, insert( V2, replaceall (E2, TS1), TS3) ) .


--- insertTrans(T1, T2): insert all variables from T1 into T2`,' overwriting values in T2
--- EXAMPLE: rew insertTrans( ( "x" |> int(4) ), ("x" |> int(5), "y" |> int (4) ) ) .
op insertTrans : TSubst TSubst -> TSubst .
eq insertTrans( TnoSubst, TS2) = TS2 .
eq insertTrans( (V1 |> E1, TS1), TS2) = insertTrans( TS1, insert (V1, E1, TS2) ) .


--- appendTrans(TS1, TS2) :  append TS2 to TS1.  first`,' the variables 
--- in TS2 are replaced by the expressions in TS1`,' then the definitions 
--- from TS2 are taken and put into TS1`,' overwriting the assignments 
--- if there are new ones in TS2
--- EXAMPLE rew appendTrans( ( "x" |> "+"("x" :: int(1))), ("z" |> "x") ) .
---         rew appendTrans( ( "x" |> "+"("x" :: int(1))), ("z" |> "x", "x" |> int(3) ) ) .
--- NOTE:  variables on the LHS give the new values`,' while variables 
---        on the RHS are the values at the start of execution - 
--- like a normal assign statement
op appendTrans : TSubst TSubst -> TSubst .
eq appendTrans ( TS1, TS2 ) = insertTrans(insertValues( TS1, TS2 ), TS1 ) .



----------------------------------------------------------------------
---  replace variables by expressions in expression
----------------------------------------------------------------------
--- replace in the first expression the variable denoted by the second expression by the third expression
--- expl: rew replace ("&&"("<"("m" :: "mmax") :: "<"("-"("mfree" :: "t") :: "/"("m" :: "mrate"))), "m", "nte") .
op replace : Expr Expr Expr -> Expr .

eq replace ( "~" (E1), V1, E2 ) = "~" (replace (E1, V1, E2) ) . 
eq replace ( "-" (E1), V1, E2 ) = "-" (replace (E1, V1, E2) ) . 
eq replace ( "#" (E1), V1, E2 ) = "#" (replace (E1, V1, E2) ) . 
eq replace ( "head" (E1), V1, E2 ) = "head" (replace (E1, V1, E2) ) .
eq replace ( "tail" (E1), V1, E2 ) = "tail" (replace (E1, V1, E2) ) .
eq replace ( "+" (E3 :: E4) , V1, E2  ) = "+" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "-" (E3 :: E4) , V1, E2  ) = "-" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "*" (E3 :: E4) , V1, E2  ) = "*" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "/" (E3 :: E4) , V1, E2  ) = "/" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "%" (E3 :: E4) , V1, E2  ) = "%" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "**" (E3 :: E4) , V1, E2 ) = "**" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "<" (E3 :: E4) , V1, E2  ) = "<" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "<=" (E3 :: E4) , V1, E2 ) = "<=" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( ">" (E3 :: E4) , V1, E2  ) = ">" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( ">=" (E3 :: E4) , V1, E2 ) = ">=" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "|-" (E3 :: E4) , V1, E2 ) = "|-" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "|-|" (E3 :: E4) , V1, E2 ) = "|-|" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "&&" (E3 :: E4) , V1, E2 ) = "&&" ( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .

eq replace ( "&&" (E3 :: E4 :: neEL), V1, E2) = replace ( "&&" ( replace ( "&&" (E3 :: E4) , V1, E2) :: neEL ), V1, E2 ) .

--- eq replace ( "=" (E3 :: E4) , V1, E2 )  = bool( replace(E3, V1, E2) == replace (E4, V1, E2 ) ) .
--- eq replace ( "/=" (E3 :: E4) , V1, E2 ) = bool( replace(E3, V1, E2) =/= replace (E4, V1, E2 ) ) .
eq replace ( "=" (E3 :: E4) , V1, E2 )  = "="( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .
eq replace ( "/=" (E3 :: E4) , V1, E2 ) = "/="( replace(E3, V1, E2) :: replace (E4, V1, E2 ) ) .


ceq replace ( V1, V1, E2 ) = E2 if not ``substr(V1, sd(length(V1),5), 5)'' == "_init" .
ceq replace ( V1, V1, E2 ) = V1 if  ``substr(V1, sd(length(V1),5), 5)'' == "_init" .
---ceq replace ( V2, V1, E2 ) = V2 if not V1 == V2 .
eq replace ( E1, V1, E2 ) = E1 [owise].


--- replace all variables in E1 by the mappings in Tsubst.
op replaceall : Expr  TSubst -> Expr .
eq replaceall(E1, (V2 |> E2 , TS1) ) = replaceall(replace(E1, V2, E2), TS1 ) .
eq replaceall(E1, TnoSubst) = E1 .


--- generate a helper map to rename the variables
 op genRenameHelper : Subst String TSubst -> TSubst .
 eq genRenameHelper (noSubst, Q, TS1) = TS1 .
 eq genRenameHelper ((  C |-> E1 , S ), Q, TS1) = genRenameHelper( S, Q, insert(C, (Q + C), TS1) ) .

----------------------------------------------------------------------
--- rename variables in a list
----------------------------------------------------------------------
--- renameLHS( S, A, TS1) = rename the LHS of TS1 by prepending A if
--- the Vid is in the keyset of S.  Dont change the other keys.
--- EXAMPLE rew renameLHS ( ( "s" |-> int(4), "d" |-> int(4) ) , "pre", ( "s" |> "sd", "ff" |> "fs") ) .
 op renameLHS : Subst String TSubst -> TSubst .
 eq renameLHS( noSubst, Q, TS1 ) = TS1 .
 eq renameLHS( (  C |-> E1 , S ), Q, ( TS1, C |> E2) ) = renameLHS( S, Q, insert(  ( Q + C  ) , E2, TS1 ) ) .
 eq renameLHS( (  C |-> E1 , S ), Q,  TS1 ) = renameLHS(S, Q, TS1)  [owise] .

--- renameRHS(TS1, TS2) = rename variables in the RHS of TS2 by
--- the replacemap in TS1.
--- example rew renameRHS( genRenameHelper( ("sd" |-> int(0) ), "pre" ) , ( "s" |> "+"( "sd" :: int(2) ), "ff" |> "fs") ) .
 op renameRHS : TSubst TSubst -> TSubst .
 eq renameRHS( TS1,  ( C |> E1, TS2) ) = insert( C, replaceall(E1, TS1), renameRHS(TS1, TS2) ) .
 eq renameRHS( TS1, TnoSubst) = TnoSubst .

--- rename the variables in transitions
 op renTrans1 : Subst String TSubst -> TSubst .
 eq renTrans1(S, Q, TS1) = renameRHS(genRenameHelper(S, Q, TnoSubst), renameLHS(S, Q, TS1) ) .
 eq renTrans1(noSubst, Q, TS1) = TS1 .
--- renTrans( S, L, TS1) = rename the variables in TS1 according to the local and global variables.
--- EXAMPLE: rew renTrans( "s" |-> int(3), "f" |-> int(4) , ( "s" |> "f" ) ) .
 op renTrans : Subst Subst TSubst -> TSubst . 
 eq renTrans(S, L, TS1) = renTrans1(S, getThis(S)  + ".", renTrans1(L, getLabel((L,S)) + ".", TS1) ) .

----------------------------------------------------------------------
--- rename the variables in a statement
----------------------------------------------------------------------
 op renStmt1 : Subst String Stmt -> Stmt .
 eq renStmt1(S, Q, assign(AL ; EL ) ) 
  = assign ( renvlist(genRenameHelper(S, Q, TnoSubst), AL) ; renelist(genRenameHelper(S, Q, TnoSubst), EL) ) .

 op renStmt : Subst Subst Stmt -> Stmt .
 eq renStmt(S, L, assign( AL ; EL ) ) 
  = renStmt1( S, getThis(S) + ".", renStmt1(L, getLabel((L,S)) + ".", assign( AL ; EL ) ) ) .

--- ren the variables in an expressionlist TODO:special case of replace?
 op renelist : TSubst ExprList -> ExprList .
 eq renelist( TS1, emp ) = emp .
 eq renelist( TS1, ( E1 :: EL ) ) = ( replaceall(E1, TS1) :: renelist(TS1, EL ) ) .

--- ren the variables in an variableslist TODO:special case of replace?
 op renvlist : TSubst VidList -> VidList .
 eq renvlist( TS1, noVid) = noVid .
 eq renvlist( TS1, (V1, AL) ) = ( replaceall(V1, TS1) , renvlist(TS1, AL) ) .

----------------------------------------------------------------------
--- rename the variables in an expression
----------------------------------------------------------------------

--- Example rew renExpr( "s" |-> int(2), "f" |-> int(3), "+" ( "s" :: "f" ) ) .
--- replaceall(E, genRenameHelper("f" |-> int(3), getLabel(("f" |-> int(3),"s" |-> int(2)))))
--- rew replaceall( "+" ("s" :: "f") , genRenameHelper("f" |-> int(3), getLabel(("f" |-> int(3),"s" |-> int(2))), TnoSubst)) .
--- rew renExpr( "mmax" |-> int(2), noSubst,  "&&"("<"("m" :: "mmax") :: "<"("-"("mfree" :: "t") :: "/"("m" :: "mrate"))) ) .
op renExpr : Subst Subst Expr -> Expr .
eq renExpr(S, L, E) 
 = replaceall(replaceall(E, genRenameHelper(L, getLabel((L,S)) + ".", TnoSubst)), 
               genRenameHelper(S, getThis( (L,S)) + ".", TnoSubst) ) .


----------------------------------------------------------------------
--- generate the Transition Relation of an assign statement
----------------------------------------------------------------------

--- compute the transition of an expression:
--- EXAMPLE genTrans(assign("x" ; "+" ("x" :: int(1) ) ) ) .
--- EXAMPLE appending two assignments: rew appendTrans( genTrans(assign("x" ; "+" ("x" :: int(1) ) ) ) , genTrans(assign("z" ; "x") )  ) .
op size : TSubst -> Nat .
eq size(TS1) = sizeR (TS1, 0) .

op sizeR : TSubst Nat -> Nat .
eq sizeR(TnoSubst, F ) = F .
eq sizeR((TS1, C |> E2), F) = sizeR(TS1, F + 1) .
 
op genTrans : Stmt -> TSubst .
eq genTrans( transstmt ) = genTransR ( transstmt , TnoSubst ) .

op genTransR : Stmt TSubst -> TSubst .
eq genTransR(assign( (V1, AL) ; emp ) , trans ) 
   = V1 |> list(emp) . ---weird special case when an empty list is assigned
eq genTransR(assign( (V1, AL) ; (E1 :: EL) ) , trans ) 
   = genTransR ( assign( AL ; EL ) , insert (V1, E1, trans) ) .
eq genTransR(call(A ; E ; Q ; emp ), trans ) = trans .
eq genTransR(call(A ; E ; Q ; (E1 :: EL) ), trans ) 
   = genTransR(call(A ; E ; Q ; EL ), insert(string(size(trans),10), E1, trans ) ) .
eq genTransR(new(A ; CC ; emp ), trans) = trans .
eq genTransR(new(A ; CC ; (E1 :: EL) ), trans) 
   = genTransR(new(A ; CC ; EL), insert(string(size(trans), 10), E1, trans) ) .
eq genTransR(return( emp ), trans) = trans .
eq genTransR(return((E1 :: EL) ), trans ) 
   = genTransR(return( EL), insert( string(size(trans), 10), E1, trans ) ) .
eq genTransR(noStmt , trans ) = trans .

----------------------------------------------------------------------
--- handle the new statements $marker and $rmarker
----------------------------------------------------------------------

--- returnmarker`,' handeled like normal marker`,' but label is different
rl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $rmarker(CC, CLabel) ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
   =>
   POSTLOG(` $marker(CC) ', `"$marker"', `TnoSubst', "dest" |> "return" + CLabel )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F > 
   [label returnmarker] .

--- normal marker for calls
crl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $marker(CC) ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
   =>
   POSTLOG(` $marker("call " + CC) ', `"$marker"', `TnoSubst', ( "dest" |> getLabel((L,S)) ) )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F > 
   if $hasMapping(L`,' ".label")
   [label marker] .

--- marker for calls from the initialing code that is introduced by the interpreter
crl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $marker(CC) ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
   =>
   POSTLOG(` $marker("internal " + CC) ', `"$marker"', `toTrans(L)', ( "dest" |> getThis(S) ) )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F > 
   if $hasMapping(S`,' "this") and not $hasMapping(L`,' ".label")
   [label interpretermarker] .

----------------------------------------------------------------------
--- combine the logobjects
----------------------------------------------------------------------
ceq
  <log From: 0 To: G  Type: "lastrun" Data: { CSL |   ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "$marker"  Data: {  SL | TnoSubst |  inits } Att:  S Label: C >
  <log From: F To: F1 Type: "passing" Data: { SL1 | TnoSubst |    TS2 } Att: S' Label: CC >
  =
  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL | ctrans | cinits } Att: CS Label: CLabel > 
  if (inits["dest"] == TS2["dest"]) and F < G
  [label combinemarker] .

ceq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: F  To: F1 Type: "passing" Data: { SL1 |    TS1 |    TS2 } Att: L' Label: CC >
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; EL) |    TS3 |    TS4 } Att: S' Label: C >
  =
  <log From: 0 To: ( G + 1 )  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; getParams(TS1) ) | genTrans(assign(AL ; getParams(TS1) )) | inits } Att: S' Label: C > 
  if inits["dest"] == TS2["dest"] and (F < G) .

ceq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: F  To: F1 Type: "passing" Data: { SL1 |    TS1 |    TS2 } Att: L' Label: CC >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S' Label: C >
  =
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: (G1 + 1) Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: F  To: F1 Type: "passing" Data: { SL1 |    TS1 |    TS2 } Att: L' Label: CC >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S' Label: C >
  if inits["dest"] == TS2["dest"] 
  [owise] . 



rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "ifthenelse"    Data: {  SL |  trans |  "eq" |> E } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "ifthenelse" Data: { SL | trans |  "eq" |> replaceall(E, ctrans) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  <choice Number: G Type: "ifthenelse" Expression: replaceall(E, ctrans) > 
  [label callpassing] .

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "await"    Data: {  SL |  trans |  "eq" |> E } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "await" Data: { SL | ctrans |  "eq" |> replaceall(E, ctrans) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  <choice Number: G Type: "await" Expression: replaceall(E, ctrans) > 
  [label callpassing] .

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "blocked await"    Data: {  SL |  trans |  "eq" |> E } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "blocked await" Data: { SL | ctrans |  "eq" |> replaceall(E, ctrans) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  <choice Number: G Type: "blocked await" Expression: replaceall(E, ctrans) > 
  [label callpassing] .

rl 
  <choice Number: G Type: "ifthenelse" Expression: bool(true) > 
  => none .

rl
  <log From: G To: G1 Type: "ifthenelse"    Data: {  SL |  trans |  "eq" |> bool(true) } Att:  S Label: C >
  => none .

--- replace the call by an adjusted passing opject and skip it by lastrun
rl 
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "call"    Data: {  SL |  trans |  inits } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "passing" Data: { skip | insertValues(ctrans, trans) |  inits } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  [label callpassing] .

--- replace a create by an adjusted passing opject and skip it by lastrun
rl
 <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
 <log From: G To: G1 Type: "create"  Data: {  SL |  trans |  inits } Att:  S Label: C >
 =>
 <log From: G To: G1 Type: "passing" Data: { skip | insertValues(ctrans, trans) |  inits } Att: S Label: C > 
 <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  CSL ; SL | ctrans | cinits } Att: CS Label: CLabel > 
 [label createpassing] .

--- replace a return by an adjusted passing opject and skip it by lastrun
rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "return"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "passing" Data: { skip | insertValues(ctrans, trans) |  inits } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  CSL ; SL | ctrans | cinits } Att: CS Label: CLabel > 
  [label returnpassing] .

--- combine assign
rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "assign"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  =>
  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL ; SL | appendTrans(ctrans, trans) | cinits } Att: CS Label: CLabel > 
 [label combineassign] .
)dnl


    --- assignment
    ---
    --- Execute an assignment.  First, all expressions on the left hand side
    --- of the assignment are evaluated and the statement is rewritten to
    --- an assign form.
STEP(dnl
PRELOG`'dnl
`< O : C | Att: S, Pr: { L | assign(AL ; EL) ; SL },
	    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >' CLOCK,
POSTLOG(` renStmt(S, L, assign(AL ; EL)) ', `"assign"', ` renTrans(S, L, genTrans(assign( AL ; EL )) ) ', `TnoSubst')`'dnl
`< O : C | Att: S, Pr: { L | $assign(AL ; EVALLIST(EL, (S :: L), T)) ; SL }, 
	    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >' CLOCK,
`[label assignment]')

eq
  < O : C | Att: S, Pr: { L | $assign((Q @ CC), AL ; D :: DL) ; SL },
    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
    < O : C | Att: insert(Q, D, S), Pr: { L | $assign(AL ; DL) ; SL },
      PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > 
  [label do-static-assign] .

eq
  < O : C | Att: S, Pr: { L | $assign( (Q, AL) ; D :: DL) ; SL },
    PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  if $hasMapping(L, Q) then
    < O : C | Att: S, Pr: { insert(Q, D, L) | $assign(AL ; DL) ; SL },
      PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > 
  else
    < O : C | Att: insert(Q, D, S), Pr: { L | $assign(AL ; DL) ; SL },
      PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  fi
  [label do-assign] .



--- Skip
---
STEP(dnl
`< O : C | Att: S, Pr: { L | skip ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
   Lcnt: F >',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >',
`[label skip]')


--- Commit a transaction.
    rl
      < O : C | Att: S, Pr: { L | commit ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
        Lcnt: F >
      =>
      < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
      [label commit] .

--- if_then_else
---
STEP(dnl
PRELOG`'dnl
< O : C | Att: S`,' Pr: { L | if E th SL1 el SL2 fi ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
  CLOCK,
if EVAL(E, (S :: L), T) asBool then
    < O : C | Att: S`,' Pr: { L | SL1 ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
POSTLOG(`if E th skip el skip fi', `"ifthenelse"', `TnoSubst', "eq" |> renExpr(S, L, E) ) dnl
  else
    < O : C | Att: S`,' Pr: { L | SL2 ; SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
POSTLOG(`if E th skip el skip fi', `"ifthenelse"', `TnoSubst', "eq" |> "~"(renExpr(S, L, E)) ) dnl
  fi
  CLOCK,
`[label if-then-else]')


--- while
---
--- During model checking we want to be able to observe infinite loops.
--- Therefore, it is always a rule.
---
rl
  < O : C | Att: S, Pr: { L | while E do SL1 od ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =>
  < O : C | Att: S,
            Pr: { L | if E th (SL1 ; while E do SL1 od) el skip fi ; SL },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label while] .


--- Non-deterministic choice
---
--- Choice is comm, so [choice] considers both SL1 and SL2.
---
crl
  < O : C | Att: S, Pr: { L | (SL1 [] SL2); SL }, PrQ: W, Dealloc: LS,
            Ev: MM, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { L | SL1 ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
            Lcnt: F > CLOCK
  if READY(SL1, (S :: L), MM, T)
  [label choice] .


ifdef(`WITH_MERGE',
`    --- Merge
    ---
    --- Merge is comm, so [merge] considers both SL1 and SL2.
    ---
    crl
      < O : C | Att: S, Pr: { L | (SL1 ||| SL2); SL }, PrQ: W, Dealloc: LS,
                Ev: MM, Lcnt: F > CLOCK
      =>
      < O : C | Att: S, Pr: { L | (SL1 MERGER SL2); SL }, PrQ: W, Dealloc: LS,
                Ev: MM, Lcnt: F > CLOCK
      if READY(SL1,(S :: L), MM, T)
      [label merge] .

    --- merger
    ---
    eq
      < O : C | Att: S,  Pr:  { L | ((ST ; SL1) MERGER SL2); SL }, PrQ: W,
                Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
      =
      if ENABLED(ST, (S :: L), MM, T) then
        < O : C | Att: S, Pr: { L | ((ST ; (SL1 MERGER SL2)); SL) }, PrQ: W,
          Dealloc: LS, Ev: MM, Lcnt: F >
      else
        < O : C | Att: S, Pr: { L | ((ST ; SL1) ||| SL2); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >   
      fi CLOCK
     [label merger] .')


--- PROCESS SUSPENSION

--- release
---
--- The release statement is an unconditional processor release point.
---
STEP(dnl
`< O : C | Att: S, Pr: { L | release ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >',
`< O : C | Att: S, Pr: idle, PrQ: W , { L | SL }, Dealloc: LS, Ev: MM, Lcnt: F >',
`[label release]')


--- suspend
---
CSTEP(dnl
`< O : C | Att: S, Pr: { L | SST ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: F > CLOCK',
`< O : C | Att: S, Pr: idle, PrQ: W , { L | SST ; SL}, Dealloc: LS, Ev: MM,
           Lcnt: F > CLOCK',
not ENABLED(SST, (S :: L), MM, T),
`[label suspend]')


--- await
---
ifdef(`LOGGING',dnl
--- record an await whose condition is not fulfilled
crl 
  PRELOG`'dnl
  `< O : C | Att: S, Pr: { L | await E ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > '
  =>
  POSTLOG(`await E', `"blocked await"', TnoSubst, `"eq" |> renExpr(S, L, "~"(E) )' )`'dnl
  `< O : C | Att: S, Pr: { L | $bawait E ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > '
---  `< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >'
  if `not EVALGUARD(E, (S :: L), MM, T) asBool'
  `[label blockedawait]' .

crl 
  PRELOG`'dnl
  `< O : C | Att: S, Pr: { L | $bawait E ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > '
  =>
  POSTLOG(`await E', `"await"', TnoSubst, `"eq" |> renExpr(S, L, (E) )' )`'dnl
  `< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >'
  if `EVALGUARD(E, (S :: L), MM, T) asBool'
  `[label notawait]' .

)dnl
CSTEP(dnl
PRELOG`'dnl
`< O : C | Att: S, Pr: { L | await E ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: F > CLOCK',
POSTLOG(`await E', `"await"', TnoSubst, `"eq" |> renExpr(S, L, E)' )`'dnl
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK',
`EVALGUARD(E, (S :: L), MM, T) asBool'
`[label await]')

--- Optimize label access in await statements.
eq
  < O : C | Att: S, Pr: { L | await ?(A) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | await ?(L[A]) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  .


--- Schedule a new process for execution, if it is ready.
---
--- Must be a rule to preserve confluence.
---
crl
  < O : C | Att: S, Pr: idle, PrQ: W , { L | SL }, Dealloc: LS, Ev: MM,
            Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  if READY(SL, (S :: L), MM, T)
  [label PrQ-ready] .


--- METHOD CALLS
---

--- OPTIMISATION: Reduce the value of a label in a process to avoid
--- constant re-evaluation
eq < O : C | Att: S, Pr: { L | get(A ; AL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > =
  < O : C | Att: S, Pr: { L | get(L[A] ; AL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > .


--- receive-comp
---
--- Must be a rule in the model checker, because there might be multiple
--- completion messages with the same label but different return values
--- in the queue.
---
rl
  < O : C |  Att: S, Pr: { L | get(N ; AL) ; SL }, PrQ: W, Dealloc: LS,
             Ev: (MM  + comp(N, DL)), Lcnt: F > 
  =>
  < O : C |  Att: S, Pr: { L | assign(AL ; DL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label receive-comp] .


--- local-reply
---
CSTEP(dnl
`< O : C | Att: S, Pr: { L | get(N ; AL) ; SL }, PrQ: W , { L''` | SL1 }, Dealloc: LS, Ev: MM, Lcnt: F >',
`< O : C | Att: S, Pr:  { L''` | SL1 ; $cont N },
  PrQ: W , { L | get(N ; AL) ; SL }, Dealloc: LS, Ev: MM, Lcnt: F >',
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
    Dealloc: LS, Ev: MM, Lcnt: F >
  =>
  < O : C | Att: S, Pr: { L' | get(N ; AL) ; SL1 }, PrQ: W,
    Dealloc: LS, Ev: MM, Lcnt: F >
  [label continue] .


--- local-async-static-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; "" ; EL ); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, label(O, O, Q, EVALLIST(EL, (S :: L), T)), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  bindMtd(O`,' O`,' label(O, O, Q, EVALLIST(EL, (S :: L), T))`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
,
`rl
  < O : C | Att: S, Pr: { L | static( A ; Q ; CC ; "" ; EL ); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  =>
  < O : C | Att: S, Pr: { insert (A, label(O, F), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: (F + 1) >
  bindMtd(O`,' O`,' label(O, F)`,' Q`,' EVALLIST(EL, (S :: L), T)`,' CC < emp >) CLOCK'
)dnl
  [label local-async-static-call] .


--- remote-async-call
---
ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  =
  < O : C | Att: S, Pr: { insert(A, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  invoc(O, label(O, EVAL(E, (S :: L), T), Q, EVALLIST(EL, (S :: L), T)), Q, EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
,dnl
`rl
  PRELOG`'dnl
  < O : C | Att: S, Pr: { L | call(A ; E ; Q ; EL); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  =>
  POSTLOG(`call(A ; E ; Q ; EL)', `"call"' , renTrans(S, L, genTrans(call(A ; E ; Q ; EL))), ("dest" |> toString(label(O, F)) ) )dnl
  < O : C | Att: S, Pr: { insert(A, label(O, F), L) | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: (F + 1) > CLOCK
  invoc(O, label(O, F), Q , EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
)dnl
  [label remote-async-call] .


STEP(`< O : C | Att: S, Pr: { L | multicast(E ; Q ; EL) ; SL }, PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: F > CLOCK',
`< O : C | Att: S, Pr: { L | $multicast(EVAL(E, (S :: L), T) ; Q ; EVALLIST(EL, (S :: L), T)) ; SL }, PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: F > CLOCK',
`[label multicast-eval]')

eq 
  < O : C | Att: S, Pr: { L | $multicast(list(emp) ; Q ; DL) ; SL }, PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label multicast-emit-list-emp] .

ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | $multicast(list('O'` :: DL) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(list(DL) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: (label(O, 'O'`, Q, DL2) ^ LS), Ev: MM, Lcnt: F >
  invoc(O, label(O, 'O'`, Q, DL2), Q, DL2) from O to' O',
`eq
  < O : C | Att: S, Pr: { L | $multicast(list('O'` :: DL) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(list(DL) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: (label(O, F) ^ LS), Ev: MM, Lcnt: (F + 1) >
  invoc(O, label(O, F), Q , DL2) from O to 'O')
  [label multicast-emit-list] .

eq 
  < O : C | Att: S, Pr: { L | $multicast(set(emptyset) ; Q ; DL); SL },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label multicast-emit-set-emp] .

ifdef(`MODELCHECK',
`eq
  < O : C | Att: S, Pr: { L | $multicast(set('O'` : DS) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(set(DS) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: (label(O, 'O'`, Q, DL2) ^ LS), Ev: MM, Lcnt: F >
  invoc(O, label(O, 'O'`, Q, DL2), Q, DL2) from O to 'O',
`eq
  < O : C | Att: S, Pr: { L | $multicast(set('O'` : DS) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: S, Pr: { L | $multicast(set(DS) ; Q ; DL2) ; SL },
            PrQ: W, Dealloc: (label(O, F) ^ LS), Ev: MM, Lcnt: (F + 1) >
  invoc(O, label(O, F), Q , DL2) from O to 'O')
  [label multicast-emit-set] .

--- return
---
STEP(PRELOG`'dnl
`< O : C |  Att: S, Pr: { L | return(EL); SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK',
POSTLOG(`return(EL)', `"return"', renTrans(S, L, genTrans(return(EL) ) ), ` "dest" |> "return" + getLabel((L,S))')dnl
`< O : C |  Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK
  comp(L[".label"], EVALLIST(EL, (S :: L), T)) from O to caller(L[".label"])',
`[label return]')


--- transport
---
--- Transport rule: include new message in queue
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  cmsg from O' to O
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: (MM + cmsg), Lcnt: F >
  [label transport-cmsg] .

eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  invoc(O', N, Q, DL) from O' to O
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  bindMtd(O, O', N, Q, DL, C < emp >)
  [label transport-imsg] .

--- free
---
--- Free a label.  Make sure that the use of labels is linear.
---
STEP(< O : C | Att: S`,' Pr: { L | free(A) ; SL }`,' PrQ: W`,'
               Dealloc: LS`,' Ev: MM`,' Lcnt: F >,
  < O : C | Att: S`,' Pr: { insert(A`,' null`,' L) | SL }`,' PrQ: W`,'
            Dealloc: (L[A] ^ LS)`,' Ev: MM`,' Lcnt: F >,
  `[label free]')


--- deallocate
---
eq
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: (N ^ LS),
            Ev: (MM + comp(N, DL)), Lcnt: F >
  =
  < O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  [label deallocate] .


--- TAIL CALLS
---
--- Fake the caller and the label and tag the label.  Since we do not
--- want to interleave, this can also be an equation.
---
STEP(`< O : C | Att: S, Pr: { L | tailcall(E ; Q ; EL) ; SL }, PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  invoc(O, L[".label"], Q, EVALLIST(EL, (S :: L), T)) from O to EVAL(E, (S :: L), T)'
  CLOCK,
`[label tailcall]')

--- STATIC TAIL CALLS
---
--- Fake the caller and the label and tag the label.  Since we do not
--- want to interleave, this can also be an equation.
---
STEP(`< O : C | Att: S, Pr: { L | statictail(Q ; "" ; "" ; EL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept tag(L[".label"])  }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), C < emp >)'
  CLOCK,
`[label local-tailcall]')

STEP(`< O : C | Att: S, Pr: { L | statictail(Q ; CC ; "" ; EL) ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >' CLOCK,
`< O : C | Att: S, Pr: { noSubst | $accept tag(L[".label"]) }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  bindMtd(O, O, tag(L[".label"]), Q, EVALLIST(EL, (S :: L), T), CC < emp >)'
  CLOCK,
`[label static-tailcall]')

*** If we receive the method body, the call is accepted and the label untagged.
crl
  < O : C | Att: S, Pr: { noSubst | $accept N }, PrQ: W , { L | SL },
         Dealloc: LS, Ev: MM, Lcnt: F >
  =>
  < O : C | Att: S, Pr: { insert(".label", tag(N), L) | SL }, PrQ: W,
            Dealloc: LS, Ev: MM, Lcnt: F >
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
ifdef(`LOGGING',dnl
--- A $marker identifies the start of execution of a method.  Assignment 
--- of parameters to local variables was changed from $assign to assign 
--- to enable logging for it.

,)dnl
STEP(dnl
PRELOG`'dnl
< O : C | Att: S`,'Pr: { L | new (A ; CC ; EL); SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F > 
  < CC : Class | Inh: I `,' Param: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: G >
  CLOCK`'dnl
,dnl
POSTLOG(`new (A ; CC ; EL)', `"create"', renTrans(S, L, genTrans(new(A ; CC ; EL ) ) ), `"dest" |> CC + string(G, 10) ' )dnl
< O : C | Att: S`,' Pr: { L | assign(A ; newId(CC`,' G)); SL }`,' PrQ: W`,' Dealloc: LS`,' Ev: MM`,' Lcnt: F >
  < CC : Class | Inh: I `,' Param: AL`,' Att: S' `,' Mtds: MS `,' Ocnt: (G + 1) >
  < newId(CC`,'G) : CC | Att: S`,' Pr: idle`,' PrQ: noProc`,' Dealloc: noDealloc`,' Ev: noMsg`,' Lcnt: 0 >
  findAttr(newId(CC`,' G)`,' I`,' S'`,' 
    MARKER("createmarker " + CC + string(G, 10))ifdef(`LOGGING',,`$')assign(AL ; EVALLIST(EL, compose(S`,'  L), T))`,'
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
  < O : C | Att: S, Pr: idle, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  =
  < O : C | Att: ("this" |-> O, S'), Pr: { L' | SL ; SL1 }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > .



--- assert
---
STEP(dnl
`< O : C | Att: S, Pr: { L | assert(E) ; SL }, PrQ: W, Dealloc: LS, Ev: MM,
           Lcnt: F > CLOCK',
`if EVALGUARD(E, (S :: L), MM, T) asBool then
    < O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >
  else
    < O : C | Att: S, Pr: { L | failure(E) ; SL }, PrQ: W, Dealloc: LS,
      Ev: MM, Lcnt: F >
  fi CLOCK',
`[label assert]')



--- REAL-TIME CREOL
---
--- posit
---
ifdef(`TIME',dnl
`CSTEP(
`< O : C | Att: S, Pr: { L | posit E ; SL }, PrQ: W,
           Dealloc: LS, Ev: MM, Lcnt: F > CLOCK',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > CLOCK',
EVALGUARD(E, (S :: L), MM, T) asBool,
`[label posit]')',
`STEP(
`< O : C | Att: S, Pr: { L | posit E ; SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >',
`< O : C | Att: S, Pr: { L | SL }, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F >',
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
eq posit (c:Class cnf, T) = posit (cnf, T) .
eq posit (< O : C | Att: S, Pr: P, PrQ: W, Dealloc: LS, Ev: MM, Lcnt: F > cnf, T) =
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
