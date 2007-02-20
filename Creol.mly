(** Grammar file for Creol.

    This file is an input file to the menhir parser generator. *)


%token EOF
%token CLASS CONTRACTS INHERITS IMPLEMENTS BEGIN END NEW
%token INTERFACE WITH OP VAR IN OUT
%token EQEQ COMMA SEMI COLON ASSIGN RBRACK LBRACK LPAREN RPAREN
(* %token LBRACE RBRACE *)
%token QUESTION BANG BOX MERGE DOT
(* %token DIAMOND *)
(* %token BAR *)
(* %token DOTDOT *)
%token IF THEN ELSE FI SKIP AWAIT
%token AND OR XOR IFF NOT PLUS MINUS TIMES DIV EQ NE LT LE GT GE
%token <string> CID ID
%token <int>  INT
%token <bool> BOOL
%token <float> FLOAT
%nonassoc EQ NE
%left AND OR XOR IFF
%left LE LT GT GE
%left PLUS MINUS
%left TIMES DIV
%right NOT
%start <'a list> main
%{
open Creol
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
	    meth_outpars = outs; meth_body = None} }
    | OP i = ID p = parameters_opt {
	match p with
	    (ins, outs) ->
	      { meth_name = i; meth_coiface = ""; meth_inpars = ins;
		meth_outpars = outs; meth_body = None} }

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
      d = method_decl EQEQ a = loption(terminated(attributes, SEMI)) s = statement {
	{ meth_name = d.meth_name; meth_coiface = d.meth_coiface;
	  meth_inpars = d.meth_inpars; meth_outpars = d.meth_outpars;
	  meth_body = Some s} }

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
      s = choice_statement { s }

choice_statement:
      s = merge_statement { s }
    | l = merge_statement BOX r = choice_statement { Choice(l, r) }

merge_statement:
      s = compound_statement { s }
    | l = compound_statement MERGE r = merge_statement { Merge(l, r) }

compound_statement:
      s = basic_statement { s }
    | l = basic_statement SEMI r = compound_statement { Sequence(l, r) }

basic_statement:
      SKIP { Skip }
    | t = ID ASSIGN e = expression { Assign(t, e) }
    | t = ID ASSIGN NEW c = CID l = loption(delimited(LPAREN, separated_nonempty_list(COMMA, expression), RPAREN)) { New(t, c, l) }
    | IF e = expression THEN t = statement ELSE f = statement FI {
	If(e, t, f) }
    | IF e = expression THEN t = statement FI { If(e, t, Skip) }
    | AWAIT g = guard { Await g }
    | l = ioption(terminated(ID, BANG)) c = expression DOT m = ID loption(delimited(LPAREN, separated_list(COMMA, expression), RPAREN)) { Skip }
    | l = ioption(terminated(ID, BANG)) c = expression DOT m = ID LPAREN i = separated_list(COMMA, expression) SEMI o = separated_nonempty_list(COMMA, ID) RPAREN { Skip }
    | LPAREN s = statement RPAREN { s }

guard:
      l = ID QUESTION { Label l }
    | l = ID QUESTION AND g = guard { Conjunction (Label l, g) }
    | e = expression { Condition e }

expression:
      l = expression o = binop r = expression { Binary(o, l, r) }
    | NOT  e = expression { Unary(Not, e) }
    | MINUS e = expression %prec NOT { Unary(UMinus, e) }
    | i = INT { Int i }
    | f = FLOAT { Float f }
    | b = BOOL { Bool b }
    | i = ID { Id i }
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
