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





let creol_to_xml ~name ~stmt_handler ~expr_handler ~type_handler ~tree =
  let writer = XmlTextWriter.to_file name 0 in
  let rec creol_declaration_to_xml =
    function
	Class c -> creol_class_to_xml c
      | Interface i -> creol_interface_to_xml i
      | Datatype d -> creol_datatype_to_xml d
      | Exception e -> creol_exception_to_xml e
  and creol_exception_to_xml e =
    XmlTextWriter.start_element writer "creol:exception";
    XmlTextWriter.write_attribute writer "name" e.Exception.name;
    if e.Exception.parameters <> [] then
      begin
	XmlTextWriter.start_element writer "creol:parameters";
	List.iter (creol_vardecl_to_xml)
	  e.Exception.parameters;
	XmlTextWriter.end_element writer
      end ;
    XmlTextWriter.end_element writer
  and creol_datatype_to_xml d =
    XmlTextWriter.start_element writer "creol:datatype";
    XmlTextWriter.write_attribute writer "name" d.Datatype.name;
    XmlTextWriter.end_element writer
  and creol_class_to_xml c =
    XmlTextWriter.start_element writer "creol:class";
    XmlTextWriter.write_attribute writer "name" c.Class.name;
    XmlTextWriter.start_element writer "creol:parameters";
    List.iter (creol_vardecl_to_xml)
      c.Class.parameters;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:inherits";
    List.iter (creol_inherits_to_xml) c.Class.inherits;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:contracts";
    List.iter (creol_contracts_to_xml) c.Class.contracts;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:implements";
    List.iter (creol_implements_to_xml) c.Class.implements;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:attributes";
    List.iter (creol_vardecl_to_xml) c.Class.attributes;
    XmlTextWriter.end_element writer;
    List.iter (creol_with_to_xml)
      c.Class.with_defs;
    XmlTextWriter.end_element writer
  and creol_interface_to_xml i =
    XmlTextWriter.start_element writer "creol:interface";
    XmlTextWriter.write_attribute writer "name" i.Interface.name;
    XmlTextWriter.end_element writer
  and creol_with_to_xml w =
    XmlTextWriter.start_element writer "creol:with";
    begin
      match w.With.co_interface with
	  None -> XmlTextWriter.write_attribute writer "cointerface" "None"
	| Some i -> XmlTextWriter.write_attribute writer "cointerface" i
    end;
    List.iter (creol_method_to_xml)
      w.With.methods;
    XmlTextWriter.end_element writer
  and creol_inherits_to_xml (i, l) =
    XmlTextWriter.start_element writer "creol:inherits";
    XmlTextWriter.write_attribute writer "name" i;
    List.iter (creol_argument_to_xml) l;
    XmlTextWriter.end_element writer
  and creol_contracts_to_xml i =
    ()
  and creol_implements_to_xml i =
    ()
  and creol_method_to_xml m =
    XmlTextWriter.start_element writer "creol:method" ; 
    XmlTextWriter.write_attribute writer "name" m.meth_name;
    XmlTextWriter.start_element writer "creol:inputs" ; 
    List.iter (creol_vardecl_to_xml) m.meth_inpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:outputs" ; 
    List.iter (creol_vardecl_to_xml) m.meth_outpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:variables" ; 
    List.iter (creol_vardecl_to_xml) m.meth_vars;
    XmlTextWriter.end_element writer;
    (match m.meth_body with
	None -> ()
      | Some s -> XmlTextWriter.start_element writer "creol:body" ; 
	  creol_statement_to_xml s;
	  XmlTextWriter.end_element writer) ;
    XmlTextWriter.end_element writer
  and creol_statement_to_xml =
    function
	Skip a ->
	  XmlTextWriter.start_element writer "creol:skip" ; 
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Assert (a, e) ->
	  XmlTextWriter.start_element writer "creol:assert" ; 
	  creol_expression_to_xml e ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Assign (a, vs, es) ->
	  XmlTextWriter.start_element writer "creol:assign" ;
	  XmlTextWriter.start_element writer "creol:targets" ;
	  List.iter (function v -> 
	    XmlTextWriter.start_element writer "creol:variable" ;
	    XmlTextWriter.write_attribute writer "name" v ;
            XmlTextWriter.end_element writer ) vs ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:expressions" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Await (a, g) -> 
	  XmlTextWriter.start_element writer "creol:await" ;
	  creol_expression_to_xml g ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Release a -> 
	  XmlTextWriter.start_element writer "creol:release" ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | AsyncCall (a, l, c, m, es) ->
	  XmlTextWriter.start_element writer "creol:asynccall" ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "label" n ) ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  XmlTextWriter.start_element writer "creol:callee" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a  ;
          XmlTextWriter.end_element writer
      | Reply (a, l, is) ->
	  XmlTextWriter.start_element writer "creol:reply" ;
	  XmlTextWriter.write_attribute writer "label" l ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter (function i -> 
	    XmlTextWriter.start_element writer "creol:variable" ;
	    XmlTextWriter.write_attribute writer "name" i ;
            XmlTextWriter.end_element writer ) is ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Free (a, l) ->
	  XmlTextWriter.start_element writer "creol:free" ;
	  XmlTextWriter.write_attribute writer "label" l ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | SyncCall (a, c, m, es, is) ->
	  XmlTextWriter.start_element writer "creol:synccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  XmlTextWriter.start_element writer "callee" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter (function i -> 
	    XmlTextWriter.start_element writer "creol:variable" ;
	    XmlTextWriter.write_attribute writer "name" i ;
            XmlTextWriter.end_element writer ) is ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | AwaitSyncCall (a, c, m, es, is) ->
	  XmlTextWriter.start_element writer "creol:awaitsynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  XmlTextWriter.start_element writer "callee" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter (function i -> 
	    XmlTextWriter.start_element writer "creol:variable" ;
	    XmlTextWriter.write_attribute writer "name" i ;
            XmlTextWriter.end_element writer ) is ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | LocalAsyncCall (a, l, m, lb, ub, es) ->
	  XmlTextWriter.start_element writer "creol:localasynccall" ;
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
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | LocalSyncCall (a, m, l, u, es, is) ->
	  XmlTextWriter.start_element writer "creol:localsynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match u with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter (function i -> 
	    XmlTextWriter.start_element writer "creol:variable" ;
	    XmlTextWriter.write_attribute writer "name" i ;
            XmlTextWriter.end_element writer ) is ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | AwaitLocalSyncCall (a, m, l, u, es, is) ->
	  XmlTextWriter.start_element writer "creol:awaitlocalsynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match u with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter (function i -> 
	    XmlTextWriter.start_element writer "creol:variable" ;
	    XmlTextWriter.write_attribute writer "name" i ;
            XmlTextWriter.end_element writer ) is ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Tailcall (a, m, l, u, es) ->
	  XmlTextWriter.start_element writer "creol:tailcall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match u with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | If (a, c, t, f) ->
	  XmlTextWriter.start_element writer "creol:if" ;
	  XmlTextWriter.start_element writer "creol:condition" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:then" ;
	  creol_statement_to_xml t ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:else" ;
	  creol_statement_to_xml f ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | While (a, c, i, d) ->
	  XmlTextWriter.start_element writer "creol:while" ;
	  XmlTextWriter.start_element writer "creol:condition" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  begin
	    match i with
		None -> ()
	      | Some inv ->
		  XmlTextWriter.start_element writer "creol:invariant" ;
		  creol_expression_to_xml inv ;
		  XmlTextWriter.end_element writer ;
	  end ;
	  XmlTextWriter.start_element writer "creol:do" ;
	  creol_statement_to_xml d ;
          XmlTextWriter.end_element writer ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Sequence (a, s1, s2) ->
	  XmlTextWriter.start_element writer "creol:sequence" ;
	  creol_statement_to_xml s1;
	  creol_statement_to_xml s2;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Merge (a, f, n) ->
	  XmlTextWriter.start_element writer "creol:merge" ;
	  creol_statement_to_xml f ;
	  creol_statement_to_xml n ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
      | Choice (a, f, n) ->
	  XmlTextWriter.start_element writer "creol:choice" ;
	  creol_statement_to_xml f ;
	  creol_statement_to_xml n ;
	  stmt_handler writer a ;
          XmlTextWriter.end_element writer
  and creol_vardecl_to_xml v =
    XmlTextWriter.start_element writer "creol:vardecl";
    XmlTextWriter.write_attribute writer "name" v.var_name;
    creol_type_to_xml v.var_type;
    (match v.var_init with
	None -> ()
      | Some e -> creol_argument_to_xml e) ;
    XmlTextWriter.end_element writer
  and creol_argument_to_xml e =
    XmlTextWriter.start_element writer "creol:argument" ; 
    creol_expression_to_xml e;
    XmlTextWriter.end_element writer
  and creol_expression_to_xml =
    function
	Expression.Null a -> 
	  XmlTextWriter.start_element writer "creol:null" ; 
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Nil a -> 
	  XmlTextWriter.start_element writer "creol:nil" ; 
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Bool (a, v) -> 
	  XmlTextWriter.start_element writer "creol:bool" ; 
	  XmlTextWriter.write_attribute writer "value" (string_of_bool v) ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Int (a, v) -> 
	  XmlTextWriter.start_element writer "creol:int" ; 
	  XmlTextWriter.write_attribute writer "value" (string_of_int v) ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Float (a, v) -> 
	  XmlTextWriter.start_element writer "creol:float" ; 
	  XmlTextWriter.write_attribute writer "value" (string_of_float v) ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.String (a, v) -> 
	  XmlTextWriter.start_element writer "creol:string" ; 
	  XmlTextWriter.write_attribute writer "value" v ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Id (a, v) -> 
	  XmlTextWriter.start_element writer "creol:identifier" ; 
	  XmlTextWriter.write_attribute writer "value" v ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Unary (a, o, f) -> 
	  XmlTextWriter.start_element writer "creol:unary" ; 
	  XmlTextWriter.write_attribute writer "operator" 
	    (Expression.string_of_unaryop o) ;
	  XmlTextWriter.start_element writer "creol:argument" ;
	  creol_expression_to_xml f ;
          XmlTextWriter.end_element writer ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Binary (a, o, f, s) -> 
	  XmlTextWriter.start_element writer "creol:binary" ; 
	  XmlTextWriter.write_attribute writer "operator"
	    (Expression.string_of_binaryop o);
	  XmlTextWriter.start_element writer "creol:first" ;
	  creol_expression_to_xml f ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:second" ;
	  creol_expression_to_xml s ;
          XmlTextWriter.end_element writer ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.FuncCall (a, f, es) -> 
	  XmlTextWriter.start_element writer "creol:funccall" ; 
	  XmlTextWriter.write_attribute writer "name" f ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e ->
	    XmlTextWriter.start_element writer "creol:argument" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.FieldAccess (a, e, f) ->
	  XmlTextWriter.start_element writer "creol:fieldaccess" ; 
	  XmlTextWriter.write_attribute writer "name" f ;
	  creol_expression_to_xml e ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
      | Expression.Label (a, l) ->
	  XmlTextWriter.start_element writer "creol:label" ;
	  XmlTextWriter.write_attribute writer "name" l;
	  expr_handler writer a ;
	  XmlTextWriter.end_element writer
      | Expression.New (a, c, es) ->
	  XmlTextWriter.start_element writer "creol:new" ;
	  XmlTextWriter.write_attribute writer "class" (Type.as_string c) ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  expr_handler writer a ;
          XmlTextWriter.end_element writer
  and creol_type_to_xml =
    function
	Type.Basic (a, s) ->
	  XmlTextWriter.start_element writer "creol:type" ; 
          XmlTextWriter.write_attribute writer "name" s ;
	  type_handler writer a ;
          XmlTextWriter.end_element writer
      | Type.Application (a, s, l) ->
	  XmlTextWriter.start_element writer "creol:typeapplication" ; 
          XmlTextWriter.write_attribute writer "name" s ;
	  List.iter creol_type_to_xml l;
	  type_handler writer a ;
          XmlTextWriter.end_element writer
      | Type.Variable (a, s) ->
	  XmlTextWriter.start_element writer "creol:typevariable" ; 
          XmlTextWriter.write_attribute writer "name" s ;
	  type_handler writer a ;
          XmlTextWriter.end_element writer
      | Type.Label a ->
	  XmlTextWriter.start_element writer "creol:label" ; 
	  type_handler writer a ;
          XmlTextWriter.end_element writer
  in
    XmlTextWriter.set_indent writer true;
    XmlTextWriter.start_document writer None None None;
    XmlTextWriter.start_element writer "creol:creol";
    XmlTextWriter.write_attribute writer "version" "0.0";
    XmlTextWriter.write_attribute writer "exporter"
      (Version.package ^ " " ^ Version.version);
    List.iter (creol_declaration_to_xml) tree;
    XmlTextWriter.end_element writer;
    XmlTextWriter.end_document writer;
    XmlTextWriter.flush writer
