(** Grammar file for Creol.

    This file is an input file to the menhir parser generator. *)


%token EOF
%token CLASS CONTRACTS INHERITS IMPLEMENTS BEGIN END NEW
%token INTERFACE WITH OP VAR IN OUT WAIT
%token EQEQ COMMA SEMI COLON ASSIGN RBRACK LBRACK LPAREN RPAREN
%token LBRACE RBRACE
%token QUESTION BANG BOX MERGE DOT
(* %token DIAMOND *)
(* %token BAR *)
(* %token DOTDOT *)
%token IF THEN ELSE FI SKIP AWAIT
%token AND OR XOR IFF NOT PLUS MINUS TIMES DIV EQ NE LT LE GT GE
%token <string> CID ID STRING
%token <int>  INT
%token <bool> BOOL
%token <float> FLOAT
%token NIL NULL
%nonassoc EQ NE
%left AND OR XOR IFF
%left LE LT GT GE
%left PLUS MINUS
%left TIMES DIV
%right NOT
%left SEMI
%left MERGE
%left BOX
%start <'a list> main
%{
open Creol

let default = ()
%}
%%

main:
      d = declarations EOF { d }
    | EOF { [] }

declarations:
      d = declaration { [d] }
    | d = declaration l = declarations { d::l }

declaration:
      d = classdecl { Class d }
    | d = interfacedecl	{ Interface d }

classdecl:
      CLASS n = CID p = cls_parameters_opt
	c = loption(preceded(CONTRACTS, separated_nonempty_list(COMMA, CID)))
	i = loption(preceded(INHERITS, separated_nonempty_list(COMMA, inherits)))
	j = loption(preceded(IMPLEMENTS, separated_nonempty_list(COMMA, CID)))
	BEGIN a = attributes m = methods_opt END {
      { cls_name = n; cls_parameters = p; cls_inherits = i;
	cls_contracts = c; cls_implements = j; cls_attributes = a;
	cls_methods = m } }

cls_parameters_opt:
      (* empty *) { [] }
    | LPAREN l = separated_nonempty_list(COMMA, vardecl_no_init) RPAREN { l }

inherits:
      i = CID { (i, []) }
    | i = CID LPAREN e = separated_nonempty_list(COMMA, expression) RPAREN { (i, e) }

attributes:
      VAR l = separated_nonempty_list(COMMA, vardecl) { l }
    | l1 = attributes VAR l2 = separated_nonempty_list(COMMA, vardecl) { l1 @ l2 }

vardecl:
      v = vardecl_no_init { v }
    | v = vardecl_no_init ASSIGN i = expression
    { { var_name = v.var_name; var_type = v.var_type; var_init = Some i } }

vardecl_no_init:
      i = ID COLON t = creol_type { { var_name = i; var_type = t; var_init = None } }

method_decl:
      WITH m = CID OP i = ID p = parameters_opt {
	match p with (ins, outs) ->
	  { meth_name = i; meth_coiface = m; meth_inpars = ins;
	    meth_outpars = outs; meth_vars = []; meth_body = None} }
    | OP i = ID p = parameters_opt {
	match p with
	    (ins, outs) ->
	      { meth_name = i; meth_coiface = ""; meth_inpars = ins;
		meth_outpars = outs; meth_vars = []; meth_body = None} }

parameters_opt:
      (* empty *) { ([], []) }
    | LPAREN ins = inputs RPAREN { (ins, []) }
    | LPAREN outs = outputs RPAREN { ([], outs) }
    | LPAREN ins = inputs SEMI outs = outputs RPAREN { (ins, outs) }

inputs:
      IN l = separated_nonempty_list(COMMA, vardecl_no_init) { l }

outputs:
      OUT l = separated_nonempty_list(COMMA, vardecl_no_init) { l }

method_def:
      d = method_decl; EQEQ; a = loption(terminated(attributes, SEMI));
	s = statement ioption(SEMI)
    { { meth_name = d.meth_name; meth_coiface = d.meth_coiface;
	  meth_inpars = d.meth_inpars; meth_outpars = d.meth_outpars;
	  meth_vars = a; meth_body = Some s} }

methods_opt:
      (* empty *) { [] }
    | m = methods { m }

methods:
      m = method_def { [m] }
    | m = method_def l = methods { m::l }

interfacedecl:
      INTERFACE n = CID i = iface_inherits_opt BEGIN m = method_decls_opt END {
	{ iface_name = n; iface_inherits = i; iface_methods = m } }

iface_inherits_opt:
      (* empty *) { [] }
    | INHERITS l = separated_nonempty_list(COMMA, ID) { l }

method_decls_opt:
      (* empty *) { [] }
    | m = method_decls { m }

method_decls:
      m = method_decl { [m] }
    | m = method_decl l = method_decls { m::l }

(* Statements *)
statement:
      SKIP { Skip default }
    | t = delimited(LBRACK, separated_nonempty_list(COMMA, ID), RBRACK) ASSIGN
	e = delimited(LBRACK, separated_nonempty_list(COMMA, expression), RBRACK)
	{ Assign(default, t, e) }
    | t = ID ASSIGN e = expression { Assign(default, [t], [e]) }
    | t = ID ASSIGN NEW c = CID;
	l = delimited(LPAREN, separated_list(COMMA, expression), RPAREN)
        { New(default, t, c, l) }
    | IF e = expression THEN t = statement ELSE f = statement FI
        { If(default, e, t, f) }
    | IF e = expression THEN t = statement FI
        { If(default, e, t, Skip default) }
    | AWAIT g = guard { Await (default, g) }
    | c = ioption(terminated(expression, DOT)); m = ID;
	p = delimited(LPAREN, pair(separated_list(COMMA, expression), preceded(SEMI, separated_list(COMMA, ID))), RPAREN)
	{ let caller = match c with
	    None -> Id (default, "this")
	  | Some e -> e in
	      SyncCall (default, caller, m, fst p, snd p) }
    | l = ioption(ID) BANG c = ioption(terminated(expression, DOT)) m = ID;
	p = delimited(LPAREN, pair(separated_list(COMMA, expression), ioption(preceded (SEMI, separated_list(COMMA, ID)))), RPAREN)
	{ let caller = match c with
	    None -> Id (default, "this")
	  | Some e -> e in
	      ASyncCall (default, l, caller, m, fst p, snd p) }
    | l = ID QUESTION LPAREN o = separated_list(COMMA, ID) RPAREN
	{ Reply (default, l, o) }
    | LBRACE s = statement RBRACE { s }
    | l = statement SEMI r = statement { Sequence(default, l, r) }
    | l = statement MERGE r = statement { Merge(default, l, r) }
    | l = statement BOX r = statement { Choice(default, l, r) }

guard:
      l = ID QUESTION { Label (default, l) }
    | WAIT { Wait default }
    | l = ID QUESTION AND g = guard
        { Conjunction (default, Label(default, l), g) }
    | e = expression { Condition (default, e) }

expression:
      l = expression o = binop r = expression { Binary(default, o, l, r) }
    | NOT  e = expression { Unary(default, Not, e) }
    | MINUS e = expression %prec NOT { Unary(default, UMinus, e) }
    | f = ID LBRACK l = separated_nonempty_list(COMMA, expression) RBRACK
	{ FuncCall(default, f, l) }
    | i = INT { Int (default, i) }
    | f = FLOAT { Float (default, f) }
    | b = BOOL { Bool (default, b) }
    | id = ID { Id (default, id) }
    | s = STRING { String (default, s) }
    | NIL { Nil default }
    | NULL { Null default }
    | LPAREN e = expression RPAREN { e }

%inline binop:
      AND { And }
    | OR { Or }
    | XOR { Ne }
    | IFF { Eq }
    | EQ { Eq }
    | NE { Ne }
    | LE { Le }
    | GE { Ge }
    | LT { Lt }
    | GT { Gt }
    | PLUS { Plus }
    | MINUS { Minus }
    | TIMES { Times }
    | DIV { Div }

(* Poor mans types and type parameters *)
creol_type:
      t = CID { t }
    | t = CID LBRACK separated_nonempty_list(COMMA, creol_type) RBRACK { t } 
