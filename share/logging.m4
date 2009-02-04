vars TS1 TS2 TS3 TS4 TS5 TS6 : TSubst .
var  CLabel : String .
var  CSL : StmtList .
var CS : Subst .
vars G1 G2 G3 F1 : Nat .

----------------------------------------------------------------------
--- handle the new statements $marker and $rmarker
----------------------------------------------------------------------

--- returnmarker`,' handeled like normal marker`,' but label is different
rl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $rmarker(CC, EL, CLabel) ; SL }`,' PrQ: W`,' Lcnt: F >
   =>
   POSTLOG(` $marker(CC, EL) ', `"$marker"', `toTrans(EL)', "dest" |> "return" + CLabel )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Lcnt: F > 
   [label returnmarker] .

--- normal marker for calls
crl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $marker(CC, EL) ; SL }`,' PrQ: W`,' Lcnt: F >
   =>
   POSTLOG(` $marker("call " + CC, EL) ', `"$marker"', `toTrans(EL)', ( "dest" |> getLabel((L,S)) ) )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Lcnt: F > 
   if $hasMapping(L`,' ".label")
   [label marker] .

--- marker for calls from the initialing code that is introduced by the interpreter
crl
   PRELOG`'dnl
   < O : C | Att: S`,' Pr: { L | $marker(CC, EL) ; SL }`,' PrQ: W`,' Lcnt: F >
   =>
   POSTLOG(` $marker("internal " + CC, EL) ', `"$marker"', `toTrans(EL)', ( "dest" |> getThis(S) ) )dnl
   < O : C | Att: S`,' Pr: { L | SL }`,'  PrQ: W`,' Lcnt: F > 
   if $hasMapping(S`,' "this") and not $hasMapping(L`,' ".label")
   [label interpretermarker] .

----------------------------------------------------------------------
--- combine the logobjects
----------------------------------------------------------------------


op unpack : Expr -> ExprList .
eq unpack(list(EL)) = EL .

--- an empty marker is simply removed - ther is no according assign
eq
  <log From: 0 To: G  Type: "lastrun" Data: { CSL |   TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "$marker"  Data: {  SL | TnoSubst |  TS4 } Att:  S Label: C >
  =
  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL | TS1 | TS2 } Att: CS Label: CLabel > .

--- marker that is followed by an assign.  the label is still taken
--- from the TS4 map of marker`,' should be changed to the
--- Label-field.
eq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; EL) |    TS5 |    TS6 } Att: S1 Label: C >
  =
  <log From: 0 To: ( G + 1 )  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G1 To: G2 Type: "assign" Data: { assign(AL ; unpack(TS2[TS4["dest"]]) ) | 
   getTrans(assign(AL ; unpack(TS2[TS4["dest"]] ))) | TS4 } Att: S1 Label: C > .

--- marker that is not followed by a related assign - increase the
--- marker id until the correct assign is found

eq 
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G  To: G1 Type: "$marker"  Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS5 |    TS6 } Att: S1 Label: C >
  =
  <log From: 0  To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G  To: (G1 + 1) Type: "$marker"  Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
  <log From: G2 To: G3 Type: "assign" Data: { SL2 |    TS5 |    TS6 } Att: S1 Label: C >
  [owise] . 

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "ifthenelse"    Data: {  SL |  TS3 |  "eq" |> E } Att:  S Label: C >
  =>
---  <log From: G To: G1 Type: "ifthenelse" Data: { SL | TS3 |  "eq" |> replace(E, filter(TS1)) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | TS1 | TS2 } Att: CS Label: CLabel > 
  <choice Number: G Type: "ifthenelse" Expression: replace(E, filter(TS1)) > 
  [label callpassing] .

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "await"    Data: {  SL |  TS3 |  "eq" |> E } Att:  S Label: C >
  =>
---  <log From: G To: G1 Type: "await" Data: { SL | TS1 |  "eq" |> replace(E, filter(TS1)) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | TS1 | TS2 } Att: CS Label: CLabel > 
  <choice Number: G Type: "await" Expression: replace(E, filter(TS1)) > 
  [label callpassing] .

rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "blocked await"    Data: {  SL |  TS3 |  "eq" |> E } Att:  S Label: C >
  =>
---  <log From: G To: G1 Type: "blocked await" Data: { SL | TS1 |  "eq" |> replace(E, filter(TS1)) } Att: S Label: C > 
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | TS1 | TS2 } Att: CS Label: CLabel > 
  <choice Number: G Type: "blocked await" Expression: replace(E, filter(TS1)) > 
  [label callpassing] .


---remove awaits that just wait for a method to finish
rl <choice Number: G Type: "await" Expression: (?(E)) >
   => none .

rl <choice Number: G Type: "blocked await" Expression: "~"(?(E)) >
   => none .

rl <choice Number: G Type: "await" Expression: bool(true) >
   => none .

rl <choice Number: G Type: "blocked await" Expression: bool(true) >
   => none .

rl 
  <choice Number: G Type: "ifthenelse" Expression: bool(true) > 
  => none .

rl
  <log From: G To: G1 Type: "ifthenelse"    Data: {  SL |  TS3 |  "eq" |> bool(true) } Att:  S Label: C >
  => none .


--- replace the call by an adjusted passing object and skip it by lastrun
rl 
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "call"    Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
  =>
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  ( CSL ; SL ) | TS1 | 
   insertPassing(TS4["dest"], getParams(TS3), TS2 ) } Att: CS Label: CLabel > 
  [label callpassing] .


--- replace a create by an adjusted passing opject and skip it by lastrun
rl
 <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
 <log From: G To: G1 Type: "create"  Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
 =>
 <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  CSL ; SL | TS1 | 
  insertPassing(TS4["dest"], getParams(TS3), TS2 ) } Att: CS Label: CLabel > 
 [label createpassing] .

--- replace a return by an adjusted passing opject and skip it by lastrun
rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "return"  Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
  =>
  <log From: 0 To: (G + 1)  Type: "lastrun" Data: {  CSL ; SL | TS1 | 
   insertPassing(TS4["dest"], getParams(TS3), TS2 ) } Att: CS Label: CLabel > 
  [label returnpassing] .

--- combine assign
rl
  <log From: 0 To: G  Type: "lastrun" Data: { CSL | TS1 | TS2 } Att: CS Label: CLabel > 
  <log From: G To: G1 Type: "assign"  Data: {  SL |  TS3 |  TS4 } Att:  S Label: C >
  =>
  <log From: 0 To: G1  Type: "lastrun" Data: {  CSL ; SL | 
   appendTrans(TS1, TS3) | TS2 } Att: CS Label: CLabel > 
 [label combineassign] .
