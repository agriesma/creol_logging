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

  var logcnt : Nat .

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
eq insertValuesR( TS1, (V2 |> E2, TS2), TS3 ) = insertValuesR( TS1, TS2, insert( V2, replace (E2, TS1), TS3) ) .


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
--- handle the new statements $marker and $rmarker
----------------------------------------------------------------------

--- returnmarker`,' handeled like normal marker`,' but label is different
rl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $rmarker(CC, CLabel) ; SL }`,' PrQ: W`,' Lcnt: F >
   =>
   POSTLOG(` $marker(CC) ', `"$marker"', `TnoSubst', "dest" |> "return" + CLabel )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Lcnt: F > 
   [label returnmarker] .

--- normal marker for calls
crl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $marker(CC) ; SL }`,' PrQ: W`,' Lcnt: F >
   =>
   POSTLOG(` $marker("call " + CC) ', `"$marker"', `TnoSubst', ( "dest" |> getLabel((L,S)) ) )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Lcnt: F > 
   if $hasMapping(L`,' ".label")
   [label marker] .

--- marker for calls from the initialing code that is introduced by the interpreter
crl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $marker(CC) ; SL }`,' PrQ: W`,' Lcnt: F >
   =>
   POSTLOG(` $marker("internal " + CC) ', `"$marker"', `toTrans(L)', ( "dest" |> getThis(S) ) )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Lcnt: F > 
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
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; EL) |    TS3 |    TS4 } Att: S1 Label: C >
  =
  <log From: 0 To: ( G + 1 )  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; cinits[inits["dest"]] ) | getTrans(assign(AL ; cinits[inits["dest"]] )) | inits } Att: S1 Label: C > .

--- marker that is not followed by a related assign - increase the
--- marker id until the correct assign is found

eq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S1 Label: C >
  =
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G  To: (G1 + 1) Type: "$marker"  Data: {  SL |  trans |  inits } Att:  S Label: C >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS3 |    TS4 } Att: S1 Label: C >
  [owise] . 

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "ifthenelse"    Data: {  SL |  trans |  "eq" |> E } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "ifthenelse" Data: { SL | trans |  "eq" |> replace(E, ctrans) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  <choice Number: G Type: "ifthenelse" Expression: replace(E, ctrans) > 
  [label callpassing] .

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "await"    Data: {  SL |  trans |  "eq" |> E } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "await" Data: { SL | ctrans |  "eq" |> replace(E, ctrans) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  <choice Number: G Type: "await" Expression: replace(E, ctrans) > 
  [label callpassing] .

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | ctrans | cinits } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "blocked await"    Data: {  SL |  trans |  "eq" |> E } Att:  S Label: C >
  =>
  <log From: G To: G1 Type: "blocked await" Data: { SL | ctrans |  "eq" |> replace(E, ctrans) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | ctrans | cinits } Att: CS Label: CLabel > 
  <choice Number: G Type: "blocked await" Expression: replace(E, ctrans) > 
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
