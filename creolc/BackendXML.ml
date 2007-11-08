(*
 * BackendXML.ml -- Backend to XML
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
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

(*s Read and write Creol modes as XML files.

  The XML format is used mainly for debugging dumps. *)

open Creol

let requires = function _ -> []

let conflicts = function _ -> []

let emit ~name ~tree =
  let writer = XmlTextWriter.to_file name 0 in
  let rec creol_declaration_to_xml =
    function
	Declaration.Class c -> creol_class_to_xml c
      | Declaration.Interface i -> creol_interface_to_xml i
      | Declaration.Datatype d -> creol_datatype_to_xml d
      | Declaration.Exception e -> creol_exception_to_xml e
      | Declaration.Function f -> creol_function_to_xml f
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
    creol_type_to_xml d.Datatype.name;
    XmlTextWriter.start_element writer "creol:supertypes";
    List.iter creol_type_to_xml d.Datatype.supers;
    XmlTextWriter.end_element writer ;
    XmlTextWriter.end_element writer
  and creol_function_to_xml o =
    XmlTextWriter.start_element writer "creol:function";
    XmlTextWriter.write_attribute writer "name" o.Function.name;
    XmlTextWriter.start_element writer "creol:parameters";
    List.iter (creol_vardecl_to_xml) o.Function.parameters;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:resulttype";
    creol_type_to_xml o.Function.result_type ;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:body";
    creol_expression_to_xml o.Function.body ;
    XmlTextWriter.end_element writer;
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
    let co = Type.as_string w.With.co_interface in
      XmlTextWriter.write_attribute writer "cointerface" co ;
      List.iter (creol_method_to_xml) w.With.methods;
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
    XmlTextWriter.write_attribute writer "name" m.Method.name;
    if m.Method.location <> "" then
      XmlTextWriter.write_attribute writer "location" m.Method.location;
    XmlTextWriter.start_element writer "creol:inputs" ; 
    List.iter (creol_vardecl_to_xml) m.Method.inpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:outputs" ; 
    List.iter (creol_vardecl_to_xml) m.Method.outpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "creol:variables" ; 
    List.iter (creol_vardecl_to_xml) m.Method.vars;
    XmlTextWriter.end_element writer;
    (match m.Method.body with
	None -> ()
      | Some s -> XmlTextWriter.start_element writer "creol:body" ; 
	  creol_statement_to_xml s;
	  XmlTextWriter.end_element writer) ;
    XmlTextWriter.end_element writer
  and creol_statement_to_xml =
    function
	Statement.Skip a ->
	  XmlTextWriter.start_element writer "creol:skip" ; 
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Assert (a, e) ->
	  XmlTextWriter.start_element writer "creol:assert" ; 
	  creol_expression_to_xml e ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Prove (a, e) ->
	  XmlTextWriter.start_element writer "creol:prove" ; 
	  creol_expression_to_xml e ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Assign (a, vs, es) ->
	  XmlTextWriter.start_element writer "creol:assign" ;
	  XmlTextWriter.start_element writer "creol:targets" ;
	  List.iter creol_lhs_to_xml vs ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:expressions" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Await (a, g) -> 
	  XmlTextWriter.start_element writer "creol:await" ;
	  creol_expression_to_xml g ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Posit (a, g) -> 
	  XmlTextWriter.start_element writer "creol:posit" ;
	  creol_expression_to_xml g ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Release a -> 
	  XmlTextWriter.start_element writer "creol:release" ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.AsyncCall (a, l, c, m, s, es) ->
	  XmlTextWriter.start_element writer "creol:asynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  creol_signature_to_xml s ;
	  (match l with
	      None -> ()
	    | Some n -> creol_lhs_to_xml n ) ;
	  XmlTextWriter.start_element writer "creol:callee" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a  ;
          XmlTextWriter.end_element writer
      | Statement.Reply (a, l, is) ->
	  XmlTextWriter.start_element writer "creol:reply" ;
	  creol_expression_to_xml l ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter creol_lhs_to_xml is ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Free (a, l) ->
	  XmlTextWriter.start_element writer "creol:free" ;
	  List.iter creol_lhs_to_xml l ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Bury (a, l) ->
	  XmlTextWriter.start_element writer "creol:bury" ;
	  List.iter creol_lhs_to_xml l ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.SyncCall (a, c, m, s, es, is) ->
	  XmlTextWriter.start_element writer "creol:synccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  creol_signature_to_xml s ;
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
	  List.iter creol_lhs_to_xml is ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.AwaitSyncCall (a, c, m, s, es, is) ->
	  XmlTextWriter.start_element writer "creol:awaitsynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  creol_signature_to_xml s ;
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
	  List.iter creol_lhs_to_xml is ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.LocalAsyncCall (a, l, m, s, lb, ub, es) ->
	  XmlTextWriter.start_element writer "creol:localasynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match lb with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match ub with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  creol_signature_to_xml s ;
	  (match l with
	      None -> ()
	    | Some n -> creol_lhs_to_xml n ) ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.LocalSyncCall (a, m, s, l, u, es, is) ->
	  XmlTextWriter.start_element writer "creol:localsynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match u with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  creol_signature_to_xml s ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter creol_lhs_to_xml is ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.AwaitLocalSyncCall (a, m, s, l, u, es, is) ->
	  XmlTextWriter.start_element writer "creol:awaitlocalsynccall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match u with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  creol_signature_to_xml s ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:results" ;
	  List.iter creol_lhs_to_xml is ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Tailcall (a, m, s, l, u, es) ->
	  XmlTextWriter.start_element writer "creol:tailcall" ;
	  XmlTextWriter.write_attribute writer "method" m ;
	  (match l with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "lower" n ) ;
	  (match u with
	      None -> ()
	    | Some n -> XmlTextWriter.write_attribute writer "upper" n ) ;
	  creol_signature_to_xml s ;
	  XmlTextWriter.start_element writer "creol:arguments" ;
	  List.iter (function e -> 
	    XmlTextWriter.start_element writer "creol:expression" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) es ;
          XmlTextWriter.end_element writer ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.If (a, c, t, f) ->
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
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.While (a, c, i, d) ->
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
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Sequence (a, s1, s2) ->
	  XmlTextWriter.start_element writer "creol:sequence" ;
	  creol_statement_to_xml s1;
	  creol_statement_to_xml s2;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Merge (a, f, n) ->
	  XmlTextWriter.start_element writer "creol:merge" ;
	  creol_statement_to_xml f ;
	  creol_statement_to_xml n ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Choice (a, f, n) ->
	  XmlTextWriter.start_element writer "creol:choice" ;
	  creol_statement_to_xml f ;
	  creol_statement_to_xml n ;
	  creol_statement_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Statement.Extern (a, s) ->
	  XmlTextWriter.start_element writer "creol:extern" ;
	  XmlTextWriter.write_attribute writer "symbol" s ;
	  creol_statement_note_to_xml a ;
	  XmlTextWriter.end_element writer
  and creol_signature_to_xml (co, it, ot) =
    let creol_type_option_to_xml =
      function
	  None ->
    	    XmlTextWriter.start_element writer "creol:unknown" ;
	    XmlTextWriter.end_element writer
	| Some l -> List.iter creol_type_to_xml l
    in
      XmlTextWriter.start_element writer "creol:signature" ;
      XmlTextWriter.start_element writer "creol:cointerface" ;
      creol_type_to_xml co ;
      XmlTextWriter.end_element writer ;
      XmlTextWriter.start_element writer "creol:input-parameters" ;
      creol_type_option_to_xml it ;
      XmlTextWriter.end_element writer ;
      XmlTextWriter.start_element writer "creol:output-parameters" ;
      creol_type_option_to_xml ot ;
      XmlTextWriter.end_element writer ;
      XmlTextWriter.end_element writer
  and creol_statement_note_to_xml note =
    let emit_idset elt set =
      Statement.IdSet.iter
        (fun s ->
	  XmlTextWriter.start_element writer elt ;
	  XmlTextWriter.write_attribute writer "name" s ;
	  XmlTextWriter.end_element writer)
        set
    in
      XmlTextWriter.start_element writer "creol:statement-note" ;
      XmlTextWriter.write_attribute writer "file" note.Statement.file ;
      XmlTextWriter.write_attribute writer "line"
        (string_of_int note.Statement.line) ;
      emit_idset "creol:life-var" note.Statement.life ;
      emit_idset "creol:freed-var" note.Statement.freed ;
      emit_idset "creol:buried-var" note.Statement.buried ;
      XmlTextWriter.end_element writer
  and creol_vardecl_to_xml v =
    XmlTextWriter.start_element writer "creol:vardecl";
    XmlTextWriter.write_attribute writer "name" v.VarDecl.name;
    creol_type_to_xml v.VarDecl.var_type;
    (match v.VarDecl.init with
	None -> ()
      | Some e -> creol_argument_to_xml e) ;
    XmlTextWriter.end_element writer
  and creol_argument_to_xml e =
    XmlTextWriter.start_element writer "creol:argument" ; 
    creol_expression_to_xml e;
    XmlTextWriter.end_element writer
  and creol_lhs_to_xml =
    function
        Expression.LhsId (_, v) -> 
          XmlTextWriter.start_element writer "creol:identifier" ;
          XmlTextWriter.write_attribute writer "name" v ;
          XmlTextWriter.end_element writer
      | Expression.LhsAttr (_, n, c) ->
          XmlTextWriter.start_element writer "creol:attribute" ;
          XmlTextWriter.write_attribute writer "name" n ;
          XmlTextWriter.end_element writer
      | Expression.LhsWildcard (_, None) ->
          XmlTextWriter.start_element writer "creol:wildcard" ;
          XmlTextWriter.end_element writer
      | Expression.LhsWildcard (_, Some c) ->
          XmlTextWriter.start_element writer "creol:wildcard" ;
	  creol_type_to_xml c ;
          XmlTextWriter.end_element writer
      | Expression.LhsSSAId (_, i, v) ->
          XmlTextWriter.start_element writer "creol:ssa-name" ;
          XmlTextWriter.write_attribute writer "name" i ;
          XmlTextWriter.write_attribute writer "version" (string_of_int v) ;
          XmlTextWriter.end_element writer
  and creol_expression_to_xml =
    function
        Expression.This a -> 
	  XmlTextWriter.start_element writer "creol:this" ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.QualifiedThis (a, t) -> 
	  XmlTextWriter.start_element writer "creol:qualified-this" ;
	  creol_type_to_xml t ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Caller a -> 
	  XmlTextWriter.start_element writer "creol:caller" ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Now a -> 
	  XmlTextWriter.start_element writer "creol:now" ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Null a -> 
	  XmlTextWriter.start_element writer "creol:null" ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Nil a -> 
	  XmlTextWriter.start_element writer "creol:nil" ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.History a -> 
	  XmlTextWriter.start_element writer "creol:history" ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Bool (a, v) -> 
	  XmlTextWriter.start_element writer "creol:bool" ;
	  XmlTextWriter.write_attribute writer "value" (string_of_bool v) ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Int (a, v) -> 
	  XmlTextWriter.start_element writer "creol:int" ;
	  XmlTextWriter.write_attribute writer "value" (string_of_int v) ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Float (a, v) -> 
	  XmlTextWriter.start_element writer "creol:float" ;
	  XmlTextWriter.write_attribute writer "value" (string_of_float v) ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.String (a, v) -> 
	  XmlTextWriter.start_element writer "creol:string" ;
	  XmlTextWriter.write_attribute writer "value" v ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Tuple(a, l) ->
	  XmlTextWriter.start_element writer "creol:tuple-literal" ;
	  List.iter (function e ->
	    XmlTextWriter.start_element writer "creol:element" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) l ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.ListLit(a, l) ->
	  XmlTextWriter.start_element writer "creol:list-literal" ; 
	  List.iter (function e ->
	    XmlTextWriter.start_element writer "creol:element" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) l ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.SetLit(a, l) ->
	  XmlTextWriter.start_element writer "creol:set-literal" ; 
	  List.iter (function e ->
	    XmlTextWriter.start_element writer "creol:element" ;
	    creol_expression_to_xml e ;
            XmlTextWriter.end_element writer ) l ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Id (a, v) -> 
	  XmlTextWriter.start_element writer "creol:identifier" ; 
	  XmlTextWriter.write_attribute writer "name" v ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.StaticAttr (a, n, c) ->
	  XmlTextWriter.start_element writer "creol:staticattr" ; 
	  XmlTextWriter.write_attribute writer "name" n ;
	  creol_type_to_xml c ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Unary (a, o, f) -> 
	  XmlTextWriter.start_element writer "creol:unary" ; 
	  XmlTextWriter.write_attribute writer "operator" 
	    (Expression.string_of_unaryop o) ;
	  XmlTextWriter.start_element writer "creol:argument" ;
	  creol_expression_to_xml f ;
          XmlTextWriter.end_element writer ;
	  creol_expression_note_to_xml a ;
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
	  creol_expression_note_to_xml a ;
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
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Label (a, l) ->
	  XmlTextWriter.start_element writer "creol:label" ;
	  creol_expression_to_xml l ;
	  creol_expression_note_to_xml a ;
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
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.If (a, c, t, f) ->
	  XmlTextWriter.start_element writer "creol:if" ;
	  XmlTextWriter.start_element writer "creol:condition" ;
	  creol_expression_to_xml c ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:then" ;
	  creol_expression_to_xml t ;
          XmlTextWriter.end_element writer ;
	  XmlTextWriter.start_element writer "creol:else" ;
	  creol_expression_to_xml f ;
          XmlTextWriter.end_element writer ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.Extern (a, s) ->
	  XmlTextWriter.start_element writer "creol:extern" ; 
          XmlTextWriter.write_attribute writer "name" s ;
	  creol_expression_note_to_xml a ;
          XmlTextWriter.end_element writer
      | Expression.SSAId (n, i, v) ->
          XmlTextWriter.start_element writer "creol:ssa-name" ;
          XmlTextWriter.write_attribute writer "name" i ;
          XmlTextWriter.write_attribute writer "version" (string_of_int v) ;
	  creol_expression_note_to_xml n ;
          XmlTextWriter.end_element writer
      | Expression.Phi (n, l) ->
	  XmlTextWriter.start_element writer "creol:phi" ; 
	  List.iter creol_expression_to_xml l ;
	  creol_expression_note_to_xml n ;
          XmlTextWriter.end_element writer
  and creol_expression_note_to_xml note =
    XmlTextWriter.start_element writer "creol:expression-note" ;
    XmlTextWriter.write_attribute writer "file" note.Expression.file ;
    XmlTextWriter.write_attribute writer "line"
      (string_of_int note.Expression.line) ;
    XmlTextWriter.start_element writer "creol:inferred-type" ;
    creol_type_to_xml note.Expression.ty ;
    XmlTextWriter.end_element writer ;
    XmlTextWriter.end_element writer
  and creol_type_to_xml =
    function
	Type.Basic s ->
	  XmlTextWriter.start_element writer "creol:type" ; 
          XmlTextWriter.write_attribute writer "name" s ;
          XmlTextWriter.end_element writer
      | Type.Variable s ->
	  XmlTextWriter.start_element writer "creol:typevariable" ; 
          XmlTextWriter.write_attribute writer "name" s ;
          XmlTextWriter.end_element writer
      | Type.Application (s, l) ->
	  XmlTextWriter.start_element writer "creol:typeapplication" ; 
          XmlTextWriter.write_attribute writer "name" s ;
	  List.iter creol_type_to_xml l;
          XmlTextWriter.end_element writer
      | Type.Tuple l ->
	  XmlTextWriter.start_element writer "creol:tuple" ; 
	  List.iter creol_type_to_xml l;
          XmlTextWriter.end_element writer
      | Type.Intersection p ->
	  XmlTextWriter.start_element writer "creol:intersection" ; 
	  List.iter creol_type_to_xml p ;
          XmlTextWriter.end_element writer
      | Type.Disjunction p ->
	  XmlTextWriter.start_element writer "creol:disjunction" ; 
	  List.iter creol_type_to_xml p ;
          XmlTextWriter.end_element writer
      | Type.Function (s, t) ->
	  XmlTextWriter.start_element writer "creol:function" ; 
	  creol_type_to_xml s ;
	  creol_type_to_xml t ;
          XmlTextWriter.end_element writer
      | Type.Internal ->
	  XmlTextWriter.start_element writer "creol:internal" ; 
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
