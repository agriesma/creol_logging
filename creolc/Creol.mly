(* Grammar file for Creol.

   This file is an input file to the menhir parser generator. *)

%token EOF
%token CLASS CONTRACTS INHERITS IMPLEMENTS BEGIN END INTERFACE DATATYPE
%token WHILE VAR WITH OP IN OUT CONSTRUCTOR EXTERN
%token REQUIRES ENSURES INV SOME FORALL EXISTS HISTORY
%token IF THEN ELSE SKIP RELEASE AWAIT POSIT NEW THIS NOW CALLER
%token AS BY DO
%token EXCEPTION
%token EQEQ COMMA SEMI COLON ASSIGN
%token LBRACK RBRACK
%token LPAREN RPAREN
%token LBRACE RBRACE
%token HASH QUESTION BANG DOT AT
%token SUBTYPE SUPERTYPE DLRARROW
%token BACKTICK
%token BOX DIAMOND MERGE
%token PLUS MINUS
%token TIMESTIMES TIMES PERCENT DIV EQ NE LT LE GT GE
%token AMPAMP BAR BARBAR WEDGE VEE DARROW TILDE
%token UNDERSCORE
%token HAT BACKSLASH ASSERT PROVE
%token PREPEND CONCAT APPEND
%token <string> CID ID STRING
%token <int>  INT
%token <bool> BOOL
%token <float> FLOAT
%token NIL NULL

(* %left COMMA *)
(* %left BAR *)
%left IN
%left DLRARROW
%left DARROW
%left HAT
%left BARBAR VEE
%left AMPAMP WEDGE
%right TILDE
%nonassoc EQ NE
%nonassoc LE LT GT GE
%left BACKSLASH
%left CONCAT
%right PREPEND
%left  APPEND
%left PLUS MINUS
%left TIMES DIV PERCENT
%left TIMESTIMES
%right UMINUS HASH

%start <Creol.Declaration.t list> main

%{
(* A parser for Creol.
 *
 * This file has been generated from Creol.mly
 *
 * Creol.mly is part of creoltools
 *
 * Copyright (c) 2007 by Marcel Kyas
 *
 * The code in CreolParser.mly has been generated by the menhir parser
 * generator.  In accordance with the Lesser General Public License,
 * the generated parser as well as its source file are distributed
 * under the terms of the GPL:
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

open Lexing
open Creol
open Expression
open Statement
open Method
open VarDecl

exception Error

(** Print a short error message and abort *)
let signal_error s m = Messages.error s.pos_fname s.pos_lnum m; exit 1

(** We want to be more relaxed with contracts, implements, and inherits.
    In principle, we could allow an arbitrary list of such declarations
    and then sort it out later. *)

type super_decl =
    Contracts of Inherits.t list
  | Implements of Inherits.t list
  | Inherits of Inherits.t list

let contracts l =
  List.flatten
    (List.fold_left (fun a -> function Contracts m -> m::a | _ -> a) [] l)

let implements l =
  List.flatten
    (List.fold_left (fun a -> function Implements m -> m::a | _ -> a) [] l)

let inherits l =
  List.flatten
    (List.fold_left (fun a -> function Inherits m -> m::a | _ -> a) [] l)
%}
%%

main:
      d = list(declaration) EOF { d }

declaration:
      d = classdecl { Declaration.Class d }
    | d = interfacedecl	{ Declaration.Interface d }
    | d = datatypedecl { Declaration.Datatype d }
    | d = exceptiondecl { Declaration.Exception d }

classdecl:
      CLASS n = CID p = class_param_list s = list(super_decl)
	BEGIN a = loption(attributes) aw = loption(anon_with_def)
	m = list(with_def) END
      { { Class.name = n; parameters = p; inherits = inherits s;
	  contracts = contracts s; implements = implements s;
	  attributes = a; with_defs = aw @ m ;
	  file  = $startpos.pos_fname; line = $startpos.pos_lnum } }
    | CLASS error
	{ signal_error $startpos "syntax error: invalid class name" }
    | CLASS CID error
	{ signal_error $startpos "syntax error in class declaration" }
    | CLASS CID class_param_list list(super_decl) BEGIN error
	{ signal_error $startpos "syntax error in class body definition" }

class_param_list:
      l = loption(delimited(LPAREN, separated_nonempty_list(COMMA, vardecl_no_init), RPAREN))
        { l }
    | LPAREN error
	{ signal_error $startpos "syntax error in class/interface parameter list" }

super_decl:
      d = implements_decl { d }
    | d = contracts_decl { d }
    | d = inherits_decl { d }

contracts_decl:
      CONTRACTS l = separated_nonempty_list(COMMA, inherits)
        { (Contracts l) }
    | CONTRACTS error
	{ signal_error $startpos "syntax error in contracts list" }

implements_decl:
      IMPLEMENTS l = separated_nonempty_list(COMMA, inherits)
        { (Implements l) }
    | IMPLEMENTS error
	{ signal_error $startpos "syntax error in implements declaration" }

inherits_decl:
      INHERITS l = separated_nonempty_list(COMMA, inherits)
        { (Inherits l) }
    | INHERITS error
	{ signal_error $startpos "syntax error in inherits list" }

inherits:
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
	{ { v with VarDecl.init = Some i } }

%inline vardecl_no_init:
      i = ID COLON t = creol_type
        { { VarDecl.name = i; VarDecl.var_type = t; VarDecl.init = None } }
    | ID error
    | ID COLON error
	{ signal_error $startpos "syntax error in variable declaration" }
	

method_decl:
      OP i = ID p = parameters_opt
      ioption(preceded(REQUIRES, expression))
      ioption(preceded(ENSURES, expression))
        { Method.make_decl i (fst p) (snd p) }
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

outputs:
      OUT l = separated_nonempty_list(COMMA, vardecl_no_init) { l }

anon_with_def:
    l = nonempty_list(method_def) i = list(invariant)
    { [ { With.co_interface = Type.Internal; methods = l; invariants = i } ] }

with_def:
      WITH c = creol_type l = nonempty_list(method_def) i = list(invariant)
    { { With.co_interface = c;
	methods = List.map (Method.set_cointerface c) l;
	invariants = i } }

method_def:
      d = method_decl EQEQ a = loption(terminated(attributes, SEMI))
	s = statement
    { { d with Method.vars = a; body = Some s} }
  |   d = method_decl EQEQ EXTERN s = STRING
    { { d with body = Some (Extern (Statement.make_note $startpos, s)) } }
  |   method_decl EQEQ error
    { signal_error $startpos "Syntax error in method body" }

(* Interface Declaration *)

interfacedecl:
      INTERFACE n = CID class_param_list
      i = list(inherits_decl) BEGIN w = list(with_decl) END
        { { Interface.name = n; inherits = inherits i; with_decls = w;
	    hidden = false } }
    | INTERFACE error
    | INTERFACE CID error
	{ signal_error $startpos "syntax error in interface declaration" }

with_decl:
      WITH c = creol_type l = nonempty_list(method_decl) i = list(invariant)
     { { With.co_interface = c;
	 methods = List.map (Method.set_cointerface c) l;
	 invariants = i } }
    | WITH error
    | WITH CID error
	{ signal_error $startpos "syntax error in with block declaration" }


(* Exception declaration *)

exceptiondecl:
      EXCEPTION n = CID
        p = loption(delimited(LPAREN, separated_list(COMMA, vardecl_no_init), RPAREN))
	{ { Exception.name = n; Exception.parameters = p } }


(* Data type declaration *)

datatypedecl:
    DATATYPE t = creol_type
      s = loption(preceded(BY, separated_list(COMMA, creol_type)))
    BEGIN
      list(constructordecl) o = list(functiondecl) list(invariant)
    END
    { { Datatype.name = t; supers = s; operations = o; hidden = false } }

constructordecl:
    CONSTRUCTOR CID COLON
    loption(delimited(LPAREN, separated_nonempty_list(COMMA, creol_type), RPAREN))
    { () }

functiondecl:
    OP n = id_or_op
    p = loption(delimited(LPAREN, separated_list(COMMA, vardecl_no_init), RPAREN))
    COLON t = creol_type EQEQ e = expression
    { { Operation.name = n; parameters = p; result_type = t; body = e } }
  | OP n = id_or_op
    p = loption(delimited(LPAREN, separated_list(COMMA, vardecl_no_init), RPAREN))
    COLON t = creol_type EQEQ EXTERN s = STRING
    { { Operation.name = n; parameters = p; result_type = t;
	body = Expression.Extern (Expression.make_note $startpos, s) } }
  | OP error
  | OP id_or_op error
  | OP id_or_op
    loption(delimited(LPAREN, separated_list(COMMA, vardecl_no_init), RPAREN))
    COLON error
  | OP id_or_op
    loption(delimited(LPAREN, separated_list(COMMA, vardecl_no_init), RPAREN))
    COLON creol_type EQEQ error
    { signal_error $startpos "Syntax error in function declaration" }

id_or_op:
      i = ID { i }
    | TILDE	{ "~" }
    | MINUS	{ "-" }
    | HASH	{ "#" }
    | AMPAMP	{ "&&" }
    | WEDGE	{ "/\\" }
    | BARBAR	{ "||" }
    | VEE	{ "\\/" }
    | HAT	{ "^" }
    | DLRARROW	{ "<=>" }
    | DARROW	{ "=>" }
    | EQ	{ "=" }
    | NE	{ "/=" }
    | LE	{ "<=" }
    | GE	{ ">=" }
    | LT	{ "<" }
    | GT	{ ">" }
    | PLUS	{ "+" }
    | TIMES	{ "*" }
    | TIMESTIMES { "**" }
    | DIV	{ "/" }
    | PERCENT   { "%" }
    | PREPEND	{ "-|" }
    | APPEND	{ "|-" }
    | CONCAT	{ "|-|" }
    | BACKSLASH { "\\" }
    | IN	{ "in" }

(* Statements *)

statement:
      l = choice_statement r = ioption(preceded(MERGE, statement))
	{ match r with
	      None -> l
	    | Some s -> Merge((Statement.make_note $startpos), l, s) }

choice_statement:
      l = statement_sequence r = ioption(preceded(BOX, choice_statement))
	{ match r with
	      None -> l
	    | Some s -> Choice((Statement.make_note $startpos), l, s) }

statement_sequence:
      l = basic_statement r = ioption(preceded(SEMI, statement_sequence))
	{ match r with
	      None -> l
	    | Some s -> Sequence((Statement.make_note $startpos), l, s) }

basic_statement:
      SKIP
	{ Skip (Statement.make_note $startpos) }
    | RELEASE
	{ Release (Statement.make_note $startpos) }
    | t = separated_nonempty_list(COMMA, lhs) ASSIGN
          e = separated_nonempty_list(COMMA, expression_or_new)
	{ Assign((Statement.make_note $startpos), t, e) }
    | separated_nonempty_list(COMMA, lhs) ASSIGN error
	{ signal_error $startpos "Syntax error in assignment" }
    | AWAIT e = expression
	{ Await ((Statement.make_note $startpos), e) }
    | AWAIT error
	{ signal_error $startpos "Syntax error in await condition" }
    | POSIT e = expression
	{ Posit ((Statement.make_note $startpos), e) }
    | POSIT error
	{ signal_error $startpos "Syntax error in posit condition" }
    | l = ioption(ID) BANG callee = expression DOT m = ID
      LPAREN i = separated_list(COMMA, expression) RPAREN
	{ AsyncCall ((Statement.make_note $startpos), 
		     (match l with
                          None -> None
			| Some lab -> Some (LhsVar (Expression.make_note $startpos, lab))),
                    callee, m, Statement.default_sig, i) }
    | l = ioption(ID) BANG m = ID
	lb = ioption(preceded(SUPERTYPE, CID)) 
	ub = ioption(preceded(SUBTYPE, CID))
      LPAREN i = separated_list(COMMA, expression) RPAREN
	{ LocalAsyncCall ((Statement.make_note $startpos), 
			 (match l with
                              None -> None
			    | Some lab -> Some (LhsVar (Expression.make_note $startpos, lab))),
			  m, Statement.default_sig, lb, ub, i) }
    | l = ID QUESTION LPAREN o = separated_list(COMMA, lhs) RPAREN
	{ Reply (Statement.make_note $startpos,
		 Id (Expression.make_note $startpos, l), o) }
    | c = expression DOT; m = ID;
	LPAREN i = separated_list(COMMA, expression) SEMI
	       o = separated_list(COMMA, lhs) RPAREN
	{ SyncCall ((Statement.make_note $startpos), c, m, Statement.default_sig,  i, o) }
    | m = ID
	lb = ioption(preceded(SUPERTYPE, CID))
	ub = ioption(preceded(SUBTYPE, CID))
	LPAREN i = separated_list(COMMA, expression) SEMI
	       o = separated_list(COMMA, lhs) RPAREN
	{ LocalSyncCall((Statement.make_note $startpos), m, Statement.default_sig, lb, ub, i, o) }
    | AWAIT c = expression DOT; m = ID;
	LPAREN i = separated_list(COMMA, expression) SEMI
	       o = separated_list(COMMA, lhs) RPAREN
	{ AwaitSyncCall ((Statement.make_note $startpos), c, m, Statement.default_sig, i, o) }
    | AWAIT m = ID
	lb = ioption(preceded(SUPERTYPE, CID))
	ub = ioption(preceded(SUBTYPE, CID))
	LPAREN i = separated_list(COMMA, expression) SEMI
	       o = separated_list(COMMA, lhs) RPAREN
	{ AwaitLocalSyncCall((Statement.make_note $startpos), m, Statement.default_sig, lb, ub, i, o) }
    | BEGIN s = statement END
	{ s }
    | IF e = expression THEN t = statement ELSE f = statement END
        { If((Statement.make_note $startpos), e, t, f) }
    | IF e = expression THEN t = statement END
        { If((Statement.make_note $startpos), e, t, Skip (Statement.make_note $startpos)) }
    | WHILE c = expression inv = ioption(preceded(INV, expression)) DO
	s = statement END
	{ While (Statement.make_note $startpos, c, inv, s) }
    | ASSERT a = expression
	{ Assert (Statement.make_note $startpos, a) }
    | PROVE a = expression
	{ Assert (Statement.make_note $startpos, a) }
    | ASSERT error | PROVE error
	{ signal_error $startpos "syntax error in assertion" }
    | expression error
	{ signal_error $startpos "syntax error in statement" }

(* These expressions may occur on the left hand side of an assignment. *)
lhs:
      id = ID c = ioption(preceded(AT, creol_type))
	{ match c with
	      None -> LhsVar ((Expression.make_note $startpos), id)
	    | Some cl -> LhsAttr ((Expression.make_note $startpos), id, cl) }
    | UNDERSCORE t = ioption(preceded(AS, creol_type))
	{ LhsWildcard (Expression.make_note $startpos, t) }

expression_or_new:
      e = expression
	{ e }
    | NEW t = creol_type
      a = loption(delimited(LPAREN, separated_list(COMMA, expression), RPAREN))
	{ New (Expression.make_note $startpos, t, a) }
    | NEW error
	{ signal_error $startpos "syntax error in new statement" }

expression:
      b = BOOL
	{ Bool ((Expression.make_note $startpos), b) }
    | i = INT
	{ Int ((Expression.make_note $startpos), i) }
    | f = FLOAT
	{ Float ((Expression.make_note $startpos), f) }
    | s = STRING
	{ String ((Expression.make_note $startpos), s) }
    | CALLER
	{ Caller (Expression.make_note $startpos) }
    | NOW
	{ Now (Expression.make_note $startpos) }
    | THIS
	{ This (Expression.make_note $startpos) }
    | THIS AS i = CID
	{ QualifiedThis (Expression.make_note $startpos, Type.Basic i) }
    | NIL
	{ Nil (Expression.make_note $startpos) }
    | NULL
	{ Null (Expression.make_note $startpos) }
    | HISTORY
	{ History (Expression.make_note $startpos) }
    | id = ID c = ioption(preceded(AT, creol_type))
	{ match c with
	      None -> Id (Expression.make_note $startpos, id)
	    | Some cl -> StaticAttr (Expression.make_note $startpos, id, cl) }
    | l = ID QUESTION { Label (Expression.make_note $startpos,
			       Id (Expression.make_note $startpos, l)) }
    | LPAREN l = separated_list(COMMA, expression) RPAREN 
	{ match l with
	      [e] -> e
	    | _ -> Tuple (Expression.make_note $startpos, l) }
    | LBRACK l = separated_list(COMMA, expression) RBRACK
	{ ListLit (Expression.make_note $startpos, l) }
    | LBRACE e = separated_list(COMMA, expression) RBRACE
	{ SetLit (Expression.make_note $startpos, e) }
    | LBRACE ID COLON expression BAR expression RBRACE
	{ Null (Expression.make_note $startpos) }
    | l = expression o = binop r = expression
        { Binary((Expression.make_note $startpos), o, l, r) }
    | TILDE e = expression
        { Unary((Expression.make_note $startpos), Not, e) }
    | MINUS e = expression %prec UMINUS
	{ Unary((Expression.make_note $startpos), UMinus, e) }
    | HASH e = expression
	{ Unary((Expression.make_note $startpos), Length, e) }
    | f = function_name LPAREN l = separated_list(COMMA, expression) RPAREN
	{ FuncCall((Expression.make_note $startpos), f, l) }
    | IF c = expression THEN t = expression ELSE f = expression END
        { Expression.If (Expression.make_note $startpos, c, t, f) }
(*
    | SOME v = vardecl_no_init COLON e = expression
	{ Choose (Expression.make_note $startpos, v.VarDecl.name, v.VarDecl.var_type, e) }
    | FORALL v = vardecl_no_init COLON e = expression
	{ Forall (Expression.make_note $startpos, v.VarDecl.name, v.VarDecl.var_type, e) }
    | EXISTS v = vardecl_no_init COLON e = expression
	{ Exists (Expression.make_note $startpos, v.VarDecl.name, v.VarDecl.var_type, e) }
*)

%inline binop:
      AMPAMP { And }
    | WEDGE { Wedge }
    | BARBAR { Or }
    | VEE { Vee }
    | HAT { Xor }
    | DLRARROW { Iff }
    | DARROW { Implies }
    | EQ { Eq }
    | NE { Ne }
    | LE { Le }
    | GE { Ge }
    | LT { Lt }
    | GT { Gt }
    | PLUS { Plus }
    | MINUS { Minus }
    | TIMES { Times }
    | TIMESTIMES { Power }
    | DIV { Div }
    | PERCENT { Modulo }
    | PREPEND { Prepend }
    | APPEND { Append }
    | CONCAT { Concat }
    | BACKSLASH { Project }
    | IN { In }

%inline function_name:
      f = ID { f }

(* Types *)

creol_type:
      t = CID
	{ Type.Basic t }
    | t = CID LBRACK p = separated_list(COMMA, creol_type) RBRACK
	{ Type.Application (t, p) }
    | BACKTICK v = ID
	{ Type.Variable v }
    | LBRACK d = separated_nonempty_list(COMMA, creol_type) RBRACK
	{ Type.Tuple d }

(* Invariants *)

invariant:
    INV e = expression { e }
%%
