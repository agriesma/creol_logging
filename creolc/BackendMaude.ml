(*
 * BackendMaude.ml -- Emit a tree to Maude.
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

open Creol

type options = {
  mutable modelchecker: bool;
  mutable red_init: bool;
  mutable main: string option;
}

(** Write a Creol program as a maude term. If the program is parsable
    but not semantically correct, this function will only produce
    garbage. *)
let emit options out_channel input =
  let rec of_type =
    function
	Type.Basic n -> output_string out_channel n
      | Type.Application (n, _) -> output_string out_channel n
      | _ -> assert false
  and of_expression =
    function
	Expression.This _ -> output_string out_channel "\"this\""
      | Expression.Caller _ -> output_string out_channel "\"caller\""
      | Expression.Now _ -> output_string out_channel "now"
      | Expression.Nil _ -> output_string out_channel "list(emp)"
      | Expression.Null _ -> output_string out_channel "null"
      | Expression.Int (_, i) ->
	  output_string out_channel ("int(" ^ (string_of_int i) ^ ")")
      | Expression.Float (_, f) -> assert false
      | Expression.Bool (_, false) -> output_string out_channel "bool(false)"
      | Expression.Bool (_, true) -> output_string out_channel "bool(true)"
      | Expression.String (_, s) ->
	  output_string out_channel ("str(\"" ^ s ^ "\")")
      | Expression.Id (_, i) -> output_string out_channel ("\"" ^ i ^ "\"")
      | Expression.StaticAttr (_, a, c) ->
	  output_string out_channel ("( \"" ^ a ^ "\" @@ \"");
	  of_type c ;
	  output_string out_channel "\" )"
      | Expression.Tuple (_, l) ->
	  (* XXX: The CMC does not distinguish tuples from pairs.  On
	     the other hand, this is also conceptually bogus.  Can't
	     tuples and list be identified? *)
	  output_string out_channel "pair(" ;
	  of_expression_list l ;
	  output_string out_channel ")" ;
      | Expression.ListLit (_, l) ->
	  output_string out_channel "list(" ;
	  of_expression_list l ;
	  output_string out_channel ")" ;
      | Expression.SetLit (_, l) ->
	  output_string out_channel "list(" ;
	  of_expression_list l ; (* Hope to overload # for set in maude *)
	  output_string out_channel ")" ;
      | Expression.FuncCall(_, f, a) ->
	  output_string out_channel ("\"" ^ f ^ "\" ( " );
	  of_expression_list a;
	  output_string out_channel " )"
	    (* Queer, but parens are required for parsing Appl in ExprList. *)
      | Expression.Unary _ -> assert false
      | Expression.Binary _ -> assert false
      | Expression.Label(_, l) ->
	  output_string out_channel "( " ;
	  of_expression l ;
	  output_string out_channel " ?? )"
      | Expression.New (_, c, a) ->
	  output_string out_channel
	    ("new \"" ^ (Type.as_string c) ^ "\" ( ") ;
	  of_expression_list a ;
	  output_string out_channel " )"
      | Expression.If (_, c, t, f) ->
	output_string out_channel "(if " ;
	of_expression c ;
	output_string out_channel " th " ;
	of_expression t ;
	output_string out_channel " el " ;
	of_expression f ;
	output_string out_channel " fi)" ;
      | Expression.Extern _ -> assert false
      | Expression.SSAId _ -> assert false
      | Expression.Phi _ -> assert false
  and of_expression_list =
    (** Compile a list of expressions into the Creol Maude Machine. *)
    function
	[] -> output_string out_channel "emp"
      | [e] -> of_expression e
      | e::l -> of_expression e;
	  output_string out_channel " # ";
	  of_expression_list l
  and of_identifier_list =
    (** Convert a list of identifiers into a list of Attribute identifiers. *)
    function
	[] -> output_string out_channel "noVid"
      | [i] -> output_string out_channel ("\"" ^ i ^ "\"")
      | i::l -> output_string out_channel ("\"" ^ i ^ "\", ");
	  of_identifier_list l
  and of_lhs =
    function
	Expression.LhsVar(_, i) -> output_string out_channel ("\"" ^ i ^ "\"")
      | Expression.LhsAttr(_, i, c) ->
	  output_string out_channel ("( \"" ^ i ^ "\" @@ \"") ;
	  of_type c ;
	  output_string out_channel "\" )"
      | Expression.LhsWildcard _ -> assert false
      | Expression.LhsSSAId _ -> assert false
  and of_lhs_list =
    (** Translate a list of left hand side expressions a list of
	Attribute identifiers. *)
    function
	[] ->
	  output_string out_channel "noVid"
       | [l] -> of_lhs l
       | l::r -> of_lhs l ; output_string out_channel ", " ; of_lhs_list r
  and of_statement cls stmt =
    let open_paren prec op_prec =
      if prec < op_prec then output_string out_channel "( " ;
    and close_paren prec op_prec =
      if prec < op_prec then output_string out_channel " )" ;
    in let rec print prec =
      function
	  Statement.Skip _ -> output_string out_channel "skip"
	| Statement.Assert (_, _) -> output_string out_channel "skip"
	| Statement.Await (_, e) -> output_string out_channel "( await ";
	    of_expression e;
	    output_string out_channel " )"
	| Statement.Posit (_, e) -> output_string out_channel "( posit ";
	    of_expression e;
	    output_string out_channel " )"
	| Statement.Release _ -> output_string out_channel "release"
	| Statement.Assign (_, i, e) ->
	    of_lhs_list i;
	    output_string out_channel " ::= " ;
	    of_expression_list e
	| Statement.SyncCall _ -> assert false
	| Statement.AwaitSyncCall _ -> assert false
	| Statement.AsyncCall (_, None, _, _, _, _) -> assert false
	| Statement.AsyncCall (_, Some l, c, m, _, a) ->
	    of_lhs l ;
	    output_string out_channel " ! ";
	    of_expression c ;
	    output_string out_channel (" . \"" ^ m ^ "\" ( ") ;
	    of_expression_list a;
	    output_string out_channel " )"
	| Statement.Reply (_, l, o) ->
	    output_string out_channel "( " ;
	    of_expression l ;
	    output_string out_channel " ? ( " ;
	    of_lhs_list o;
	    output_string out_channel " ) ) "
	| Statement.Free (_, l) ->
	    output_string out_channel "free( " ;
	    of_expression_list l ;
	    output_string out_channel " )"
	| Statement.LocalSyncCall _ -> assert false
	| Statement.AwaitLocalSyncCall _ -> assert false
	| Statement.LocalAsyncCall (_, None, _, _, _, _, _) -> assert false
	| Statement.LocalAsyncCall (_, Some l, m, _, None, None, i) ->
	    (* An unqualified local synchronous call should use this in
	       order to get late binding correct. *)
	    output_string out_channel "( " ;
	    of_lhs l ;
	    output_string out_channel (" ! \"this\" . \"" ^ m ^ "\" (");
	    of_expression_list i ;
	    output_string out_channel " ) ) "
	| Statement.LocalAsyncCall (_, Some l, m, _, lb, ub, i) ->
	    output_string out_channel "( " ;
	    of_lhs l ;
	    output_string out_channel (" ! \"" ^ m ^ "\" ") ;
	    (match lb with
		None -> output_string out_channel ("@ \"" ^ cls ^ "\" ")
	      | Some n -> output_string out_channel ("@ \"" ^ n ^ "\" "));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<< \"" ^ n ^ "\" "));
	    output_string out_channel "( " ;
	    of_expression_list i;
	    output_string out_channel " ) ) "
	| Statement.Tailcall (_, m, _, l, u, i) ->
	    output_string out_channel ( "\"" ^ m ^ "\"");
	    (match l with
		None -> ()
	      | Some n -> output_string out_channel (" @ \"" ^ n ^ "\""));
	    (match u with
		None -> ()
	      | Some n -> output_string out_channel (" << \"" ^ n ^ "\""));
	    output_string out_channel " ( " ;
	    of_expression_list i;
	    output_string out_channel " )"
	| Statement.If (_, c, t, f) ->
	    output_string out_channel "if "; of_expression c;
	    output_string out_channel " th "; print 25 t;
	    output_string out_channel " el "; print 25 f;
	    output_string out_channel " fi"
	| Statement.While (_, c, _, b) ->
	    output_string out_channel "while " ;
	    of_expression c;
	    output_string out_channel " do ";
	    print 25 b;
	    output_string out_channel " od "
	| Statement.Sequence (_, s1, s2) ->
	    let op_prec = 25 in
	      open_paren prec op_prec ;
	      print op_prec s1; 
	      output_string out_channel " ; ";
	      print op_prec s2; 
	      close_paren prec op_prec
	| Statement.Merge (_, l, r) ->
	    let op_prec = 29 in
	      open_paren prec op_prec ;
	      print op_prec l; 
	      output_string out_channel " ||| ";
	      print op_prec r; 
	      close_paren prec op_prec
	| Statement.Choice (_, l, r) ->
	    let op_prec = 27 in
	      open_paren prec op_prec ;
	      print op_prec l; 
	      output_string out_channel " [] ";
	      print op_prec r; 
	      close_paren prec op_prec
	| Statement.Extern _ ->
	    (* Should have been replaced by an assignment with
	       a (special) function call. *)
	    assert false
    in print 25 stmt
  and of_attribute a =
    output_string out_channel ("(" ^ a.VarDecl.name ^ ": ");
    (match a.VarDecl.init with
	None -> output_string out_channel "null"
      | Some e -> of_expression e);
    output_string out_channel ")"
  and of_attribute_list =
    function
	[] ->  output_string out_channel "none"
      | [a] -> of_attribute a
      | a::l -> of_attribute a; output_string out_channel ", ";
	  of_attribute_list l
  and of_inherits =
    function
	(i, l) -> output_string out_channel ("\"" ^ i ^ "\" < ");
	  of_expression_list l;
	  output_string out_channel " > "
  and of_inherits_list =
    function
	[] -> output_string out_channel "noInh"
      | [i] -> of_inherits i
      | i::r -> of_inherits i;
	  output_string out_channel " ## ";
	  of_inherits_list r
  and of_parameter_list =
    function
	[] -> output_string out_channel "noVid"
      | [v] -> output_string out_channel ("\"" ^ v.VarDecl.name ^ "\"")
      | v::r -> output_string out_channel ("\"" ^ v.VarDecl.name ^ "\" , ");
	  of_parameter_list r
  and of_class_attribute_list =
    function
	[] -> output_string out_channel "noSubst" 
      | [v] -> output_string out_channel ("\"" ^ v.VarDecl.name ^ "\" |-> null")
      | v::r ->
	  output_string out_channel ("\"" ^ v.VarDecl.name ^ "\" |-> null , ");
	  of_class_attribute_list r
  and of_method_return =
    function
	[] -> output_string out_channel "emp" 
      | [n] -> output_string out_channel ("\"" ^ n.VarDecl.name ^ "\"")
      | n::l -> output_string out_channel ("\"" ^ n.VarDecl.name ^ "\" # ");
          of_method_return l
  and of_method cls m =
    output_string out_channel ("\n  < \"" ^ m.Method.meth_name ^
				  "\" : Mtdname | Param: ");
    of_parameter_list m.Method.meth_inpars;
    output_string out_channel ", Latt: " ;
    of_class_attribute_list (m.Method.meth_inpars @ m.Method.meth_outpars @ m.Method.meth_vars);
    output_string out_channel ", Code: " ;
    ( match m.Method.meth_body with
	None -> output_string out_channel "skip"
      | Some s -> of_statement cls s ;
	  output_string out_channel " ; return ( ";
	  of_method_return m.Method.meth_outpars;
	  output_string out_channel " )" ) ;
    output_string out_channel " >"
  and of_method_list cls =
    function
	[] -> output_string out_channel "noMtd" 
      | [m] -> of_method cls m
      | m::r -> of_method cls m ;
	  output_string out_channel " *" ;
	  of_method_list cls r
  and of_with_defs cls ws =
    let methods = List.flatten (List.map (function w -> w.With.methods) ws)
    in
      of_method_list cls methods
  and of_class c =
    output_string out_channel ("< \"" ^ c.Class.name ^ "\" : Cl | Inh: ");
    of_inherits_list c.Class.inherits;
    output_string out_channel ", Par: ";
    of_parameter_list c.Class.parameters;
    output_string out_channel ", Att: ";
    of_class_attribute_list (c.Class.parameters @ c.Class.attributes);
    output_string out_channel ", Mtds: ";
    of_with_defs c.Class.name c.Class.with_defs;
    output_string out_channel ", Ocnt: 0 >\n\n"
  and of_interface i = ()
  and of_exception e = ()
  and of_datatype d = ()
  and of_declaration =
    function
	Declaration.Class c -> of_class c
      | Declaration.Interface i -> of_interface i
      | Declaration.Exception e -> of_exception e
      | Declaration.Datatype d -> of_datatype d
  and of_decl_list =
    function
	[] -> output_string out_channel "noConf\n"
      | [d] -> of_declaration d
      | d::l -> of_declaration d; of_decl_list l
  in
    (** Convert an abstract syntax tree l of a creol program to a
	representation for the Maude CMC and write the result to the
	output channel out. *)
    if options.modelchecker then
      output_string out_channel "load creol-modelchecker\n"
    else
      output_string out_channel "load creol-interpreter\n";
    output_string out_channel
      ("mod PROGRAM is\npr " ^ (if options.modelchecker then
	"CREOL-MODEL-CHECKER" else "CREOL-INTERPRETER") ^
	  " .\nop init : -> Configuration [ctor] .\neq init =\n") ;
    of_decl_list input ;
    begin
      match options.main with
	  None -> ()
	| Some m ->
	    output_string out_channel ("main( \"" ^ m ^ "\" , emp )\n")
    end ;
    output_string out_channel ".\nendm\n" ;
    if options.modelchecker then
      begin
	output_string out_channel
	  ("\n\nmod PROGRAM-CHECKER is\n" ^
	      "  protecting MODEL-CHECKER .\n" ^
	      "  protecting PROGRAM .\n" ^
	      "  protecting CREOL-PREDICATES .\n" ^
	      "endm\n")
      end ;
    if options.red_init then output_string out_channel "\nred init .\n" ;
    flush out_channel
