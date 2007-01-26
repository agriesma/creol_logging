(** Grammar file for Creol.

    This file is an input file to the menhir parser generator. *)


%token EOF
%token CLASS CONTRACTS INHERITS IMPLEMENTS BEGIN END
%token INTERFACE WITH OP VAR IN OUT
%token EQEQ COMMA SEMI COLON ASSIGN LPAREN RPAREN QUESTION
%token CHOICE MERGE IF THEN ELSE FI
%token SKIP AWAIT
%token AND
%token <string>  ID
%token <int>  INT
%token <bool> BOOL
%token <float> FLOAT
%token PLUS TIMES
%left PLUS
%left TIMES
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
      CLASS n = ID p = cls_parameters_opt c = contracts_opt i = inherits_opt
    j = implements_opt BEGIN a = attributes m = methods_opt END {
      { cls_name = n; cls_parameters = p; cls_inherits = i;
	cls_contracts = c; cls_implements = j; cls_attributes = a;
	cls_methods = m } }

cls_parameters_opt:
      (* empty *) { [] }
    | LPAREN l = creol_list(vardecl_no_init, COMMA) RPAREN { l }

contracts_opt:
      (* empty *) { [] }
    | CONTRACTS l = creol_list(ID, COMMA) { l }

inherits_opt:
    (* empty *)  { [] }
    | INHERITS l = creol_list(inherits, COMMA) { l }

inherits:
      i = ID { (i, []) }
    | i = ID LPAREN e = creol_list(expression, COMMA) RPAREN { (i, e) }

implements_opt:
      (* empty *) { [] }
    | IMPLEMENTS l = creol_list(ID, COMMA) { l }

attributes:
      VAR l = creol_list(vardecl, COMMA) { l }

vardecl:
      v = vardecl_no_init { v }
    | v = vardecl_no_init ASSIGN i = expression
    { { var_name = v.var_name; var_type = v.var_type; var_init = Some i } }

vardecl_no_init:
      i = ID COLON t = ID { { var_name = i; var_type = t; var_init = None } }

method_decl:
      WITH m = ID OP i = ID p = parameters_opt {
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
      IN l = creol_list(vardecl_no_init, COMMA) { l }

outputs:
      OUT l = creol_list(vardecl_no_init, COMMA) { l }

method_def:
      d = method_decl EQEQ s = statement {
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
      INTERFACE n = ID i = iface_inherits_opt BEGIN m = method_decls_opt END {
	{ iface_name = n; iface_inherits = i; iface_methods = m } }

iface_inherits_opt:
      (* empty *) { [] }
    | INHERITS l = creol_list(ID, COMMA) { l }

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
    | l = merge_statement CHOICE r = choice_statement { Choice(l, r) }

merge_statement:
      s = compound_statement { s }
    | l = compound_statement MERGE r = merge_statement { Merge(l, r) }

compound_statement:
      s = basic_statement { s }
    | l = basic_statement SEMI r = compound_statement { Sequence(l, r) }

basic_statement:
      SKIP { Skip }
    | IF e = expression THEN t = statement ELSE f = statement FI {
	If(e, t, f) }
    | IF e = expression THEN t = statement FI { If(e, t, Skip) }
    | AWAIT g = guard { Await g }
    | LPAREN s = statement RPAREN { s }

guard:
      l = ID QUESTION { Label l }
    | l = ID QUESTION AND g = guard { Conjunction (Label l, g) }
    | e = expression { Condition e }

expression:
      i = INT { Int i }
    | f = FLOAT { Float f }
    | b = BOOL { Bool b }
    | i = ID { Id i }
    | l = expression PLUS r = expression { Binary (Plus, l, r) }
    | l = expression TIMES r = expression { Binary(Times, l, r) }





(* These productions are used for any kinds of lists and options *)
creol_list(I, S):
    i = I { [i] }
  | i = I S l = creol_list(I, S) { i::l }
