(*
 * CreolIO.ml -- Input and Output routines for Creol.
 *
 * This file is part of creolcomp
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 *)

(** Read and write Creol Programs.


    @author Marcel Kyas
    @version 0.0
    @since   0.0

  *)

open Creol
open Statement
open Declaration

let from_file name =
  (** Read the contents of a file and return an abstract syntax tree.

      @since 0.0 *)
  let lexbuf = Lexing.from_channel (open_in name) in
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = name } ;
      CreolParser.main CreolLex.token lexbuf

let rec from_files =
  (** Read the contents of a list of files and return an abstract syntax
      tree.

      @since 0.0 *)
  function
      [] -> []
    | name::rest -> (from_file name)@(from_files rest)



let from_channel channel =
  (** Read the contents of a channel and return a abstract syntax tree.

      @since 0.0 *)
  let lexbuf = Lexing.from_channel channel in
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = "*channel*" } ;
      CreolParser.main CreolLex.token lexbuf





let rec creol_to_xml name stmt_handler expr_handler tree =
  let writer = XmlTextWriter.to_file name 0 in
    XmlTextWriter.set_indent writer true;
    XmlTextWriter.start_document writer None None None;
    XmlTextWriter.start_element writer "creol";
    XmlTextWriter.write_attribute writer "version" "0.0";
    XmlTextWriter.write_attribute writer "exporter"
	(Version.package ^ " " ^ Version.version);
    List.iter (creol_declaration_to_xml writer stmt_handler expr_handler) tree;
    XmlTextWriter.end_element writer;
    XmlTextWriter.end_document writer;
    XmlTextWriter.flush writer
and creol_declaration_to_xml writer stmt_handler expr_handler =
  function
      Class c -> creol_class_to_xml writer stmt_handler expr_handler c
    | Interface i -> creol_interface_to_xml writer stmt_handler expr_handler i
    | Datatype d -> creol_datatype_to_xml writer stmt_handler expr_handler d
    | Exception e -> creol_exception_to_xml writer stmt_handler expr_handler e
and creol_exception_to_xml writer stmt_handler expr_handler e =
  XmlTextWriter.start_element writer "exception";
  XmlTextWriter.write_attribute writer "name" e.Exception.name;
  if e.Exception.parameters <> [] then
    begin
      XmlTextWriter.start_element writer "parameters";
      List.iter (creol_vardecl_to_xml writer expr_handler)
	e.Exception.parameters;
      XmlTextWriter.end_element writer
    end ;
  XmlTextWriter.end_element writer
and creol_datatype_to_xml writer stmt_handler expr_handler d =
  XmlTextWriter.start_element writer "datatype";
  XmlTextWriter.write_attribute writer "name" d.Datatype.name;
  XmlTextWriter.end_element writer
and creol_class_to_xml writer stmt_handler expr_handler c =
    XmlTextWriter.start_element writer "class";
    XmlTextWriter.write_attribute writer "name" c.Class.name;
    XmlTextWriter.start_element writer "parameters";
    List.iter (creol_vardecl_to_xml writer expr_handler)
	c.Class.parameters;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "inherits";
    List.iter (creol_inherits_to_xml writer expr_handler) c.Class.inherits;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "contracts";
    List.iter (creol_contracts_to_xml writer expr_handler) c.Class.contracts;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "implements";
    List.iter (creol_implements_to_xml writer expr_handler) c.Class.implements;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "attributes";
    List.iter (creol_vardecl_to_xml writer expr_handler) c.Class.attributes;
    XmlTextWriter.end_element writer;
    List.iter (creol_with_to_xml writer stmt_handler expr_handler)
      c.Class.with_defs;
    XmlTextWriter.end_element writer
and creol_interface_to_xml writer stmt_handler expr_handler i =
    XmlTextWriter.start_element writer "interface";
    XmlTextWriter.write_attribute writer "name" i.Interface.name;
    XmlTextWriter.end_element writer
and creol_with_to_xml writer stmt_handler expr_handler w =
  XmlTextWriter.start_element writer "with";
  begin
    match w.With.co_interface with
	None -> XmlTextWriter.write_attribute writer "co-interface" "None"
      | Some i -> XmlTextWriter.write_attribute writer "co-interface" i
  end;
  List.iter (creol_method_to_xml writer stmt_handler expr_handler)
    w.With.methods;
  XmlTextWriter.end_element writer
and creol_inherits_to_xml writer expr_handler (i, l) =
    XmlTextWriter.start_element writer "inherits";
    XmlTextWriter.write_attribute writer "name" i;
    List.iter (creol_argument_to_xml writer expr_handler) l;
    XmlTextWriter.end_element writer
and creol_contracts_to_xml writer expr_handler i =
    ()
and creol_implements_to_xml writer expr_handler i =
    ()
and creol_method_to_xml writer stmt_handler expr_handler m =
    XmlTextWriter.start_element writer "method" ; 
    XmlTextWriter.write_attribute writer "name" m.meth_name;
    XmlTextWriter.start_element writer "inputs" ; 
    List.iter (creol_vardecl_to_xml writer expr_handler) m.meth_inpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "outputs" ; 
    List.iter (creol_vardecl_to_xml writer expr_handler) m.meth_outpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "variables" ; 
    List.iter (creol_vardecl_to_xml writer expr_handler) m.meth_vars;
    XmlTextWriter.end_element writer;
    (match m.meth_body with
	None -> ()
      | Some s -> XmlTextWriter.start_element writer "body" ; 
	    creol_statement_to_xml writer stmt_handler expr_handler s;
	    XmlTextWriter.end_element writer) ;
    XmlTextWriter.end_element writer
and creol_statement_to_xml writer stmt_handler expr_handler =
  function
      Skip a ->
	XmlTextWriter.start_element writer "skip" ; 
	stmt_handler writer a;
        XmlTextWriter.end_element writer
    | Assert (a, e) ->
	XmlTextWriter.start_element writer "assert" ; 
	creol_expression_to_xml writer expr_handler e ;
	stmt_handler writer a;
        XmlTextWriter.end_element writer
    | Assign (a, vs, es) ->
	XmlTextWriter.start_element writer "assign" ;
	XmlTextWriter.start_element writer "targets" ;
	List.iter (function v -> 
	             XmlTextWriter.start_element writer "variable" ;
		     XmlTextWriter.write_attribute writer "name" v ;
        	     XmlTextWriter.end_element writer ) vs ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "expressions" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a;
        XmlTextWriter.end_element writer
    | Await (a, g) -> 
	XmlTextWriter.start_element writer "await" ;
	creol_expression_to_xml writer expr_handler g ;
	stmt_handler writer a;
        XmlTextWriter.end_element writer
    | Release a -> 
	XmlTextWriter.start_element writer "release" ;
	stmt_handler writer a;
        XmlTextWriter.end_element writer
    | AsyncCall (a, l, c, m, es) ->
	XmlTextWriter.start_element writer "asynccall" ;
	(match l with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "label" n ) ;
	XmlTextWriter.write_attribute writer "method" m ;
	XmlTextWriter.start_element writer "callee" ;
	creol_expression_to_xml writer expr_handler c ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | Reply (a, l, is) ->
	XmlTextWriter.start_element writer "reply" ;
	XmlTextWriter.write_attribute writer "label" l ;
	XmlTextWriter.start_element writer "results" ;
	List.iter (function i -> 
	             XmlTextWriter.start_element writer "variable" ;
		     XmlTextWriter.write_attribute writer "name" i ;
        	     XmlTextWriter.end_element writer ) is ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | Free (a, l) ->
	XmlTextWriter.start_element writer "free" ;
	XmlTextWriter.write_attribute writer "label" l ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | SyncCall (a, c, m, es, is) ->
	XmlTextWriter.start_element writer "synccall" ;
	XmlTextWriter.write_attribute writer "method" m ;
	XmlTextWriter.start_element writer "callee" ;
	creol_expression_to_xml writer expr_handler c ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "results" ;
	List.iter (function i -> 
	             XmlTextWriter.start_element writer "variable" ;
		     XmlTextWriter.write_attribute writer "name" i ;
        	     XmlTextWriter.end_element writer ) is ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | LocalAsyncCall (a, l, m, lb, ub, es) ->
	XmlTextWriter.start_element writer "local-async-call" ;
	XmlTextWriter.write_attribute writer "method" m ;
	(match l with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "label" n ) ;
	(match lb with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	(match ub with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | LocalSyncCall (a, m, l, u, es, is) ->
	XmlTextWriter.start_element writer "localsynccall" ;
	XmlTextWriter.write_attribute writer "method" m ;
	(match l with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	(match u with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "results" ;
	List.iter (function i -> 
	             XmlTextWriter.start_element writer "variable" ;
		     XmlTextWriter.write_attribute writer "name" i ;
        	     XmlTextWriter.end_element writer ) is ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | Tailcall (a, m, l, u, es) ->
	XmlTextWriter.start_element writer "tailcall" ;
	XmlTextWriter.write_attribute writer "method" m ;
	(match l with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	(match u with
	    None -> ()
	  | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | If (a, c, t, f) ->
	XmlTextWriter.start_element writer "if" ;
	XmlTextWriter.start_element writer "condition" ;
	creol_expression_to_xml writer expr_handler c ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "then" ;
	creol_statement_to_xml writer stmt_handler expr_handler t ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "else" ;
	creol_statement_to_xml writer stmt_handler expr_handler f ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | While (a, c, i, d) ->
	XmlTextWriter.start_element writer "while" ;
	XmlTextWriter.start_element writer "condition" ;
	creol_expression_to_xml writer expr_handler c ;
        XmlTextWriter.end_element writer ;
	begin
	  match i with
	    None -> ()
	  | Some inv ->
	      XmlTextWriter.start_element writer "invariant" ;
	      creol_expression_to_xml writer expr_handler inv ;
              XmlTextWriter.end_element writer ;
	end ;
	XmlTextWriter.start_element writer "do" ;
	creol_statement_to_xml writer stmt_handler expr_handler d ;
        XmlTextWriter.end_element writer ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | Sequence (a, sl) ->
	XmlTextWriter.start_element writer "sequence" ;
	List.iter (creol_statement_to_xml writer stmt_handler expr_handler) sl;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | Merge (a, f, n) ->
	XmlTextWriter.start_element writer "merge" ;
	creol_statement_to_xml writer stmt_handler expr_handler f ;
	creol_statement_to_xml writer stmt_handler expr_handler n ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
    | Choice (a, f, n) ->
	XmlTextWriter.start_element writer "choice" ;
	creol_statement_to_xml writer stmt_handler expr_handler f ;
	creol_statement_to_xml writer stmt_handler expr_handler n ;
	stmt_handler writer a ;
        XmlTextWriter.end_element writer
and creol_vardecl_to_xml writer expr_handler v =
    XmlTextWriter.start_element writer "vardecl";
    XmlTextWriter.write_attribute writer "name" v.var_name;
    creol_type_to_xml writer expr_handler v.var_type;
    (match v.var_init with
	  None -> ()
	| Some e -> creol_argument_to_xml writer expr_handler e) ;
    XmlTextWriter.end_element writer
and creol_argument_to_xml writer expr_handler e =
    XmlTextWriter.start_element writer "argument" ; 
    creol_expression_to_xml writer expr_handler e;
    XmlTextWriter.end_element writer
and creol_expression_to_xml writer expr_handler =
  function
      Expression.Null a -> 
	XmlTextWriter.start_element writer "null" ; 
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Nil a -> 
	XmlTextWriter.start_element writer "nil" ; 
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Bool (a, v) -> 
	XmlTextWriter.start_element writer "bool" ; 
	XmlTextWriter.write_attribute writer "value" (string_of_bool v) ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Int (a, v) -> 
	XmlTextWriter.start_element writer "int" ; 
	XmlTextWriter.write_attribute writer "value" (string_of_int v) ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Float (a, v) -> 
	XmlTextWriter.start_element writer "float" ; 
	XmlTextWriter.write_attribute writer "value" (string_of_float v) ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.String (a, v) -> 
	XmlTextWriter.start_element writer "string" ; 
	XmlTextWriter.write_attribute writer "value" v ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Id (a, v) -> 
	XmlTextWriter.start_element writer "identifier" ; 
	XmlTextWriter.write_attribute writer "value" v ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Unary (a, o, f) -> 
	XmlTextWriter.start_element writer "unary" ; 
	XmlTextWriter.write_attribute writer "operator" 
	    (Expression.string_of_unaryop o) ;
	XmlTextWriter.start_element writer "argument" ;
	creol_expression_to_xml writer expr_handler f ;
        XmlTextWriter.end_element writer ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Binary (a, o, f, s) -> 
	XmlTextWriter.start_element writer "binary" ; 
	XmlTextWriter.write_attribute writer "operator"
	    (Expression.string_of_binaryop o);
	XmlTextWriter.start_element writer "first" ;
	creol_expression_to_xml writer expr_handler f ;
        XmlTextWriter.end_element writer ;
	XmlTextWriter.start_element writer "second" ;
	creol_expression_to_xml writer expr_handler s ;
        XmlTextWriter.end_element writer ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.FuncCall (a, f, es) -> 
	XmlTextWriter.start_element writer "funccall" ; 
	XmlTextWriter.write_attribute writer "name" f ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e ->
		     XmlTextWriter.start_element writer "argument" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.FieldAccess (a, e, f) ->
	XmlTextWriter.start_element writer "FieldAccess" ; 
	XmlTextWriter.write_attribute writer "name" f ;
	creol_expression_to_xml writer expr_handler e ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
    | Expression.Label (a, l) ->
	XmlTextWriter.start_element writer "label" ;
	XmlTextWriter.write_attribute writer "name" l;
	expr_handler writer a ;
	XmlTextWriter.end_element writer
    | Expression.New (a, c, es) ->
	XmlTextWriter.start_element writer "new" ;
	XmlTextWriter.write_attribute writer "class" (Type.as_string c) ;
	XmlTextWriter.start_element writer "arguments" ;
	List.iter (function e -> 
	             XmlTextWriter.start_element writer "expression" ;
		     creol_expression_to_xml writer expr_handler e ;
        	     XmlTextWriter.end_element writer ) es ;
        XmlTextWriter.end_element writer ;
	expr_handler writer a ;
        XmlTextWriter.end_element writer
and creol_type_to_xml writer handler =
  function
      Type.Basic s ->
	XmlTextWriter.start_element writer "type" ; 
        XmlTextWriter.write_attribute writer "name" s ;
        XmlTextWriter.end_element writer
    | Type.Application (s, l) ->
	XmlTextWriter.start_element writer "typeapplication" ; 
        XmlTextWriter.write_attribute writer "name" s ;
	List.iter (creol_type_to_xml writer handler) l;
        XmlTextWriter.end_element writer
    | Type.Variable s ->
	XmlTextWriter.start_element writer "typevariable" ; 
        XmlTextWriter.write_attribute writer "name" s ;
        XmlTextWriter.end_element writer
    | Type.Label ->
	XmlTextWriter.start_element writer "label" ; 
        XmlTextWriter.end_element writer
