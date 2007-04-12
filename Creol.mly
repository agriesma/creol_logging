(* Grammar file for Creol.

   This file is an input file to the menhir parser generator. *)

%token EOF
%token CLASS CONTRACTS INHERITS IMPLEMENTS BEGIN END INTERFACE
%token WITH OP VAR IN OUT
%token EQEQ COMMA SEMI COLON ASSIGN
%token RBRACK LBRACK
%token LPAREN RPAREN
%token LBRACE RBRACE
%token QUESTION BANG BOX MERGE DOT AT UPPER
(* %token DIAMOND *)
(* %token BAR *)
(* %token DOTDOT *)
%token IF THEN ELSE FI SKIP AWAIT WAIT NEW
%token AND OR XOR IFF NOT PLUS MINUS TIMES DIV EQ NE LT LE GT GE
%token <string> CID ID STRING
%token <int>  INT
%token <bool> BOOL
%token <float> FLOAT
%token NIL NULL

%left AND OR XOR IFF
%right NOT
%nonassoc EQ NE
%left LE LT GT GE
%left PLUS MINUS
%left TIMES DIV
%right UMINUS

%start <'a list> main

%{
(* A parser for Creol.

   This file has been generated from Creol.mly

   Ceol.mly is part of creolcomp written by

   Marcel Kyas <kyas@ifi.uio.no> with contributions from
   Olaf Owe and Einar Broch Johnsen

   Copyright (c) 2007

   The code in CreolParser.mly has been generated by the menhir parser
   generator.  In accordance with the Lesser General Public License,
   the generated parser as well as its source file are distributed
   under the terms of the GPL:

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
   
   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA. *)

open Lexing
open Creol
open Statement

exception Error

(** Print a short error message and abort *)
let signal_error s m =
  output_string stderr (s.pos_fname ^ ":" ^ (string_of_int s.pos_lnum) ^ ": " ^
			m ^ "\n");
  flush stderr;
  raise Error
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
      CLASS n = CID;
        p = loption(delimited(LPAREN, separated_nonempty_list(COMMA, vardecl_no_init), RPAREN))
	i = loption(preceded(INHERITS, separated_nonempty_list(COMMA, inherits)))
	c = loption(preceded(CONTRACTS, separated_nonempty_list(COMMA, CID)))
	j = loption(preceded(IMPLEMENTS, separated_nonempty_list(COMMA, CID)))
	BEGIN a = loption(attributes) m = list(method_def) END {
      { cls_name = n; cls_parameters = p; cls_inherits = i;
	cls_contracts = c; cls_implements = j; cls_attributes = a;
	cls_methods = m } }
    | CLASS error
    | CLASS CID error
	{ signal_error $startpos "syntax error in class declaration" }

%inline inherits:
    i = CID e = loption(delimited(LPAREN, separated_nonempty_list(COMMA, expression), RPAREN))
        { (i, e) }

attributes:
      VAR l = separated_nonempty_list(COMMA, vardecl) { l }
    | l1 = attributes ioption(SEMI) VAR l2 = separated_nonempty_list(COMMA, vardecl) { l1 @ l2 }
    | VAR error
	{ signal_error $startpos "syntax error in attribute declaration" }

vardecl:
      v = vardecl_no_init
	{ v }
    | v = vardecl_no_init ASSIGN i = expression
	{ { v with var_init = Some i } }

%inline vardecl_no_init:
      i = ID COLON t = creol_type { { var_name = i; var_type = t; var_init = None } }

method_decl:
      WITH m = CID OP i = ID p = parameters_opt {
	match p with (ins, outs) ->
	  { meth_name = i; meth_coiface = Basic m; meth_inpars = ins;
	    meth_outpars = outs; meth_vars = []; meth_body = None} }
    | OP i = ID p = parameters_opt {
	match p with
	    (ins, outs) ->
	      { meth_name = i; meth_coiface = Basic ""; meth_inpars = ins;
		meth_outpars = outs; meth_vars = []; meth_body = None} }
    | WITH error
    | WITH CID error
    | WITH CID OP error
    | WITH CID OP ID error
    | OP error
    | OP ID error
	{ signal_error $startpos "syntax error in method declaration" }

parameters_opt:
      (* empty *) { ([], []) }
    | LPAREN ins = inputs RPAREN { (ins, []) }
    | LPAREN outs = outputs RPAREN { ([], outs) }
    | LPAREN ins = inputs ioption(SEMI) outs = outputs RPAREN { (ins, outs) }

inputs:
      ioption(IN) l = separated_nonempty_list(COMMA, vardecl_no_init) { l }
    | error SEMI | error OUT
	{ signal_error $startpos "syntax error in method declaration" }

outputs:
      OUT l = separated_nonempty_list(COMMA, vardecl_no_init) { l }
    | error COMMA | error RPAREN
	{ signal_error $startpos "syntax error in method declaration" }

method_def:
      d = method_decl; EQEQ; a = loption(terminated(attributes, SEMI));
	s = statement (* ioption(SEMI) *)
    { { meth_name = d.meth_name; meth_coiface = d.meth_coiface;
	  meth_inpars = d.meth_inpars; meth_outpars = d.meth_outpars;
	  meth_vars = a; meth_body = Some s} }

interfacedecl:
      INTERFACE n = CID i = iface_inherits_opt BEGIN m = method_decls_opt END {
	{ iface_name = n; iface_inherits = i; iface_methods = m } }

iface_inherits_opt:
      (* empty *) { [] }
    | INHERITS l = separated_nonempty_list(COMMA, CID) { l }

method_decls_opt:
      (* empty *) { [] }
    | m = method_decls { m }

method_decls:
      m = method_decl { [m] }
    | m = method_decl l = method_decls { m::l }

(* Statements *)

statement:
      l = choice_statement r = ioption(preceded(MERGE, statement))
	{ match r with
	      None -> l
	    | Some s -> Merge((Note.make $startpos), l, s) }

choice_statement:
      l = statement_sequence r = ioption(preceded(BOX, choice_statement))
	{ match r with
	      None -> l
	    | Some s -> Choice((Note.make $startpos), l, s) }

statement_sequence:
      l = nonempty_list(basic_statement)
	{ Sequence((Note.make $startpos), l) }

basic_statement:
      SKIP SEMI
	{ Skip (Note.make $startpos) }
    | t = separated_nonempty_list(COMMA, ID) ASSIGN e = separated_nonempty_list(COMMA, expression_or_new) SEMI
	{ Assign((Note.make $startpos), t, e) }
    | AWAIT g = guard SEMI
	{ Await ((Note.make $startpos), g) }
    | l = ioption(ID) BANG callee = expression DOT m = ID
      LPAREN i = separated_list(COMMA, expression) RPAREN
      SEMI
	{ AsyncCall ((Note.make $startpos), l, callee, m, i) }
    | l = ioption(ID) BANG m = ID
      lb = ioption(preceded(AT, CID)) ub = ioption(preceded(UPPER, CID))
      LPAREN i = separated_list(COMMA, expression) RPAREN
      SEMI
	{ LocalAsyncCall ((Note.make $startpos), l, m, lb, ub, i) }
    | l = ID QUESTION LPAREN o = separated_list(COMMA, ID) RPAREN SEMI
	{ Reply ((Note.make $startpos), l, o) }
    | c = expression DOT; m = ID;
	LPAREN i = separated_list(COMMA, expression) SEMI
	       o = separated_list(COMMA, ID) RPAREN SEMI
	{ SyncCall ((Note.make $startpos), c, m, i, o) }
    | m = ID lb = ioption(preceded(AT, CID)) ub = ioption(preceded(UPPER, CID))
	LPAREN i = separated_list(COMMA, expression) SEMI
	       o = separated_list(COMMA, ID) RPAREN SEMI
	{ LocalSyncCall((Note.make $startpos), m, lb, ub, i, o) }
    | LBRACE s = statement RBRACE ioption(SEMI)
	{ s }
    | IF e = expression THEN t = statement ELSE f = statement FI ioption(SEMI)
        { If((Note.make $startpos), e, t, f) }
    | IF e = expression THEN t = statement FI ioption(SEMI)
        { If((Note.make $startpos), e, t, Skip (Note.make $startpos)) }
    | error SEMI| error ELSE | error FI | error OP | error WITH | error END
    | error EOF
	{ signal_error $startpos "syntax error in statement" }


guard:
      l = ID QUESTION { Label ((Note.make $startpos), l) }
    | WAIT { Wait (Note.make $startpos) }
    | l = ID QUESTION AND g = guard
        { Conjunction ((Note.make $startpos), Label((Note.make $startpos), l), g) }
    | e = expression { Condition ((Note.make $startpos), e) }

expression_or_new:
      e = expression
	{ e }
    | NEW t = creol_type LPAREN a = separated_list(COMMA, expression) RPAREN
	{ New (Note.make $startpos, t, a) }

expression:
      l = expression o = binop r = expression
        { Binary((Note.make $startpos), o, l, r) }
    | NOT  e = expression { Unary((Note.make $startpos), Not, e) }
    | MINUS e = expression %prec UMINUS
	{ Unary((Note.make $startpos), UMinus, e) }
    | i = INT { Int ((Note.make $startpos), i) }
    | f = FLOAT { Float ((Note.make $startpos), f) }
    | b = BOOL { Bool ((Note.make $startpos), b) }
    | id = ID { Id ((Note.make $startpos), id) }
    | s = STRING { String ((Note.make $startpos), s) }
    | NIL { Nil (Note.make $startpos) }
    | NULL { Null (Note.make $startpos) }
    | LPAREN e = expression RPAREN { e }
    | f = function_name LPAREN l = separated_list(COMMA, expression) RPAREN
	{ FuncCall((Note.make $startpos), f, l) }

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

%inline function_name:
      f = ID { f }
    | AND { "and" }
    | OR { "or" }
    | XOR { "xor" }

(* Poor mans types and type parameters *)
creol_type:
      t = CID
	{ Basic t }
    | t = CID LBRACK p = separated_nonempty_list(COMMA, creol_type) RBRACK
	{ Application(t, p) } 
    | CID LT error { signal_error $startpos "Error in type" }

%%
