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

--- insertPassing: insert params to pass to called methods or new
--- instances.  if the list of params is empty`,' the call is ignored
op insertPassing : Vid ExprList TSubst -> TSubst .
eq insertPassing( V1 , emp , TS1 ) = TS1 .
eq insertPassing( V1 , EL , TS1 ) = insert(V1, list(EL), TS1) .


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


---eq replace( C @ CC, V1, E2) = replace ( C, V1, E2 ) .
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
 eq genRenameHelper ((  V1 |-> E1 , S ), Q, TS1) = genRenameHelper( S, Q, insert(V1, (Q + V1), TS1) ) .

----------------------------------------------------------------------
--- rename variables in a list
----------------------------------------------------------------------
--- renameLHS( S, A, TS1) = rename the LHS of TS1 by prepending A if
--- the Vid is in the keyset of S.  Dont change the other keys.
--- EXAMPLE rew renameLHS ( ( "s" |-> int(4), "d" |-> int(4) ) , "pre", ( "s" |> "sd", "ff" |> "fs") ) .
 op renameLHS : Subst String TSubst -> TSubst .
 eq renameLHS( noSubst, Q, TS1 ) = TS1 .
--- eq renameLHS( (  C @ CC |-> E1 , S), Q, TS1 ) = renameLHS( S, Q, insert(Q + C, E2, TS1 ) ) .
 eq renameLHS( (  V1 |-> E1 , S ), Q, ( TS1, V1 |> E2) ) = renameLHS( S, Q, insert(  ( Q + V1  ) , E2, TS1 ) ) .
 eq renameLHS( (  V1 |-> E1 , S ), Q,  TS1 ) = renameLHS(S, Q, TS1)  [owise] .

--- renameRHS(TS1, TS2) = rename variables in the RHS of TS2 by
--- the replacemap in TS1.
--- example rew renameRHS( genRenameHelper( ("sd" |-> int(0) ), "pre" ) , ( "s" |> "+"( "sd" :: int(2) ), "ff" |> "fs") ) .
 op renameRHS : TSubst TSubst -> TSubst .
 eq renameRHS( TS1,  ( A |> E1, TS2) ) = insert( A, replaceall(E1, TS1), renameRHS(TS1, TS2) ) .
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
--- rename the variables in a statement (TODO check: only for pretty print?)
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


---------------------
--- test only
---------------------

op rmhead : ExprList -> ExprList .
eq rmhead(E :: EL) = EL .

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
eq sizeR((TS1, V1 |> E2), F) = sizeR(TS1, F + 1) .
 
op genTrans : Stmt -> TSubst .
eq genTrans( transstmt ) = genTransR ( transstmt , TnoSubst ) .

op genTransR : Stmt TSubst -> TSubst .
eq genTransR(assign( ((C @ CC), AL ) ; EL ) , trans ) = genTransR(assign ( (C, AL ) ; EL ), trans ) . --- get rid of the @
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



--- an empty marker is simply removed - ther is no according assign
eq
  <log From: 0 To: G  Type: "lastrun" Data: { CSL |   ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "$marker"  Data: {  SL | TnoSubst |  inits } Att:  S Label: C >
  =
  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL | ctrans | cinits } Att: CS Label: CLabel > .

--- marker that is followed by an assign.  the label is still taken
--- from the inits map of marker`,' should be changed to the
--- Label-field.
eq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; EL) |    TS3 |    TS4 } Att: S' Label: C >
  =
  <log From: 0 To: ( G + 1 )  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; cinits[inits["dest"]] ) | genTrans(assign(AL ; cinits[inits["dest"]] )) | inits } Att: S' Label: C > .

--- marker that is not followed by a related assign - increase the
--- marker id until the correct assign is found

eq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S' Label: C >
  =
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: (G1 + 1) Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S' Label: C >
  [owise] . 

---- old ones

--- ceq
---  <log From: 0 To: G  Type: "lastrun" Data: { CSL |   ctrans | cinits } Att: CS Label: CLabel > 
---  <log From: G To: G1 Type: "$marker"  Data: {  SL | TnoSubst |  inits } Att:  S Label: C >
---  <log From: F To: F1 Type: "passing" Data: { SL1 | TnoSubst |    TS2 } Att: S' Label: CC >
---  =
---  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL | ctrans | cinits } Att: CS Label: CLabel > 
---  if (inits["dest"] == TS2["dest"]) and F < G
---  [label combinemarker] .
---
---ceq 
---  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
---  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
---  <log From: F  To: F1 Type: "passing" Data: { SL1 |    TS1 |    TS2 } Att: L' Label: CC >
---  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; EL) |    TS3 |    TS4 } Att: S' Label: C >
---  =
---  <log From: 0 To: ( G + 1 )  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
---  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; getParams(TS1) ) | genTrans(assign(AL ; getParams(TS1) )) | inits } Att: S' Label: C > 
---  if inits["dest"] == TS2["dest"] and (F < G) .
---
---ceq 
---  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
---  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
---  <log From: F  To: F1 Type: "passing" Data: { SL1 |    TS1 |    TS2 } Att: L' Label: CC >
---  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S' Label: C >
---  =
---  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
---  <log From: G  To: (G1 + 1) Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
---  <log From: F  To: F1 Type: "passing" Data: { SL1 |    TS1 |    TS2 } Att: L' Label: CC >
---  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S' Label: C >
---  if inits["dest"] == TS2["dest"] 
---  [owise] . 
---
--- end old ones

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


--- replace the call by an adjusted passing object and skip it by lastrun
rl 
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "call"    Data: {  SL |  trans |  inits } Att:  S Label: C >
  =>
---  <log From: G To: G1 Type: "passing" Data: { skip | insertValues(ctrans, trans) |  inits } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | insertPassing(inits["dest"], getParams(trans), cinits ) } Att: CS Label: CLabel > 
  [label callpassing] .


--- replace a create by an adjusted passing opject and skip it by lastrun
rl
 <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
 <log From: G To: G1 Type: "create"  Data: {  SL |  trans |  inits } Att:  S Label: C >
 =>
--- <log From: G To: G1 Type: "passing" Data: { skip | insertValues(ctrans, trans) |  inits } Att: S Label: C > 
 <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  CSL ; SL | ctrans | insertPassing(inits["dest"], getParams(trans), cinits ) } Att: CS Label: CLabel > 
 [label createpassing] .

--- replace a return by an adjusted passing opject and skip it by lastrun
rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "return"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  =>
---  <log From: G To: G1 Type: "passing" Data: { skip | insertValues(ctrans, trans) |  inits } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  CSL ; SL | ctrans | insertPassing(inits["dest"], getParams(trans), cinits ) } Att: CS Label: CLabel > 
  [label returnpassing] .

--- combine assign
rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "assign"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  =>
  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL ; SL | appendTrans(ctrans, trans) | cinits } Att: CS Label: CLabel > 
 [label combineassign] .
