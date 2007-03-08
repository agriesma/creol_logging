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



let rec creol_to_xml name note_handler tree =
  let writer = XmlTextWriter.to_file name 0 in
    XmlTextWriter.set_indent writer true;
    XmlTextWriter.start_document writer None None None;
    XmlTextWriter.start_element writer "creol";
    XmlTextWriter.write_attribute writer "version" "0.0";
    XmlTextWriter.write_attribute writer "exporter"
	(Version.package ^ " " ^ Version.version);
    List.iter (creol_declaration_to_xml writer note_handler) tree;
    XmlTextWriter.end_element writer;
    XmlTextWriter.end_document writer;
    XmlTextWriter.flush writer
and creol_declaration_to_xml writer note_handler =
  function
      (Class c) -> creol_class_to_xml writer note_handler c
    | (Interface i) -> creol_interface_to_xml writer note_handler i
and creol_class_to_xml writer note_handler c =
    XmlTextWriter.start_element writer "class";
    XmlTextWriter.write_attribute writer "name" c.cls_name;
    XmlTextWriter.start_element writer "parameters";
    List.iter (creol_vardecl_to_xml writer note_handler)
	c.cls_parameters;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "inherits";
    List.iter (creol_inherits_to_xml writer note_handler) c.cls_inherits;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "contracts";
    List.iter (creol_contracts_to_xml writer note_handler) c.cls_contracts;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "implements";
    List.iter (creol_implements_to_xml writer note_handler) c.cls_implements;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "attributes";
    List.iter (creol_vardecl_to_xml writer note_handler) c.cls_attributes;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "methods";
    List.iter (creol_method_to_xml writer note_handler) c.cls_methods;
    XmlTextWriter.end_element writer;
    XmlTextWriter.end_element writer
and creol_interface_to_xml writer note_handler i =
    XmlTextWriter.start_element writer "interface";
    XmlTextWriter.write_attribute writer "name" i.iface_name;
    XmlTextWriter.end_element writer
and creol_inherits_to_xml writer handler (i, l) =
    XmlTextWriter.start_element writer "inherits";
    XmlTextWriter.write_attribute writer "name" i;
    List.iter (creol_argument_to_xml writer handler) l;
    XmlTextWriter.end_element writer
and creol_contracts_to_xml writer note_handler i =
    ()
and creol_implements_to_xml writer note_handler i =
    ()
and creol_method_to_xml writer handler m =
    XmlTextWriter.start_element writer "method" ; 
    XmlTextWriter.write_attribute writer "name" m.meth_name;
    XmlTextWriter.start_element writer "cointerface" ; 
    creol_type_to_xml writer handler m.meth_coiface;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "inputs" ; 
    List.iter (creol_vardecl_to_xml writer handler) m.meth_inpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "outputs" ; 
    List.iter (creol_vardecl_to_xml writer handler) m.meth_outpars;
    XmlTextWriter.end_element writer;
    XmlTextWriter.start_element writer "variables" ; 
    List.iter (creol_vardecl_to_xml writer handler) m.meth_vars;
    XmlTextWriter.end_element writer;
    (match m.meth_body with
	None -> ()
      | Some s -> XmlTextWriter.start_element writer "body" ; 
	    creol_statement_to_xml writer handler s;
	    XmlTextWriter.end_element writer) ;
    XmlTextWriter.end_element writer
and creol_vardecl_to_xml writer handler v =
    XmlTextWriter.start_element writer "vardecl";
    XmlTextWriter.write_attribute writer "name" v.var_name;
    creol_type_to_xml writer handler v.var_type;
    (match v.var_init with
	  None -> ()
	| Some e -> creol_argument_to_xml writer handler e) ;
    XmlTextWriter.end_element writer
and creol_statement_to_xml writer handler =
  function
      Skip a ->
	XmlTextWriter.start_element writer "skip" ; 
	handler writer a;
        XmlTextWriter.end_element writer
    | _ -> ()
and creol_argument_to_xml writer handler e =
    XmlTextWriter.start_element writer "argument" ; 
    creol_expression_to_xml writer handler e;
    XmlTextWriter.end_element writer
and creol_expression_to_xml writer handler =
  function
      Null a -> 
	XmlTextWriter.start_element writer "null" ; 
	handler writer a;
        XmlTextWriter.end_element writer
    | _ -> ()
and creol_type_to_xml writer handler =
  function
      Basic s ->
	XmlTextWriter.start_element writer "type" ; 
        XmlTextWriter.write_attribute writer "name" s ;
        XmlTextWriter.end_element writer
    | Application (s, l) ->
	XmlTextWriter.start_element writer "typeapplication" ; 
        XmlTextWriter.write_attribute writer "name" s ;
	List.iter (creol_type_to_xml writer handler) l;
        XmlTextWriter.end_element writer
    | Variable s ->
	XmlTextWriter.start_element writer "typevariable" ; 
        XmlTextWriter.write_attribute writer "name" s ;
        XmlTextWriter.end_element writer
