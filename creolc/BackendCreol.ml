(*
 * BackendCreol.ml -- Emit a tree as a Creol source file.
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

let rec separated_list elt_fun sep_fun =
  (** Helper function for outputting a separated list.
      It will call [elt_fun] for each element of the list and
      [sep_fun] between each element, *)
  function
      [] -> ()
    | [s] -> elt_fun s
    | s::r ->
	elt_fun s;
	sep_fun ();
	separated_list elt_fun sep_fun r

let emit out_channel input =
  (** Write a pretty-printed tree to [out_channel].
      
      The result of [lower] cannot be printed to a valid creol
      program.  The pretty-printed result can, however, be used for
      debugging. *)
  let rec pretty_print_declaration =
    function
	Declaration.Class c -> pretty_print_class c
      | Declaration.Interface i -> pretty_print_iface i
      | Declaration.Exception e -> pretty_print_exception e
      | Declaration.Datatype d -> pretty_print_datatype d
  and pretty_print_datatype d =
    output_string out_channel ("datatype " ^ (Type.as_string d.Datatype.name));
    if d.Datatype.supers <> [] then
      begin
        output_string out_channel " by " ;
	separated_list (function t -> output_string out_channel
	  (Type.as_string t))
	  (function () -> output_string out_channel ", ") d.Datatype.supers
      end ;
    output_string out_channel "\nbegin\n" ;
    List.iter pretty_print_operation d.Datatype.operations ;
    output_string out_channel "end\n"
  and pretty_print_operation o =
    output_string out_channel ("  op " ^ o.Operation.name) ;
    if o.Operation.parameters <> [] then
      begin
        output_string out_channel " (" ;
	pretty_print_vardecls 0 "" ", " "" o.Operation.parameters ;
        output_string out_channel ")"
      end ;
    output_string out_channel
      (" : " ^ (Type.as_string o.Operation.result_type) ^ " == ") ;
    pretty_print_expression o.Operation.body ;
    output_string out_channel "\n"
  and pretty_print_exception e =
    output_string out_channel ("exception " ^ e.Exception.name) ;
    begin
      match e.Exception.parameters with
          [] -> ()
	| l -> output_string out_channel "(";
	    pretty_print_vardecls 0 "" ", " "" l;
	    output_string out_channel ")" 
    end ;
    output_string out_channel "\n"
  and pretty_print_iface i =
    output_string out_channel "interface ";
    output_string out_channel i.Interface.name;
    output_string out_channel "\nbegin\n";  
    output_string out_channel "end"
  and pretty_print_class c =
    output_string out_channel ("class " ^ c.Class.name ^ " ") ;
    if [] <> c.Class.parameters then
      begin
	output_string out_channel "(";
	pretty_print_vardecls 0 "" ", " "" c.Class.parameters ;
	output_string out_channel ")"
      end ;
    if [] <> c.Class.implements then
      begin
	output_string out_channel "\nimplements " ;
	separated_list (output_string out_channel)
	  (function () -> output_string out_channel ", ") c.Class.implements
      end;
    if [] <> c.Class.contracts then
      begin
	output_string out_channel "\ncontracts " ;
	separated_list (output_string out_channel)
	  (function () -> output_string out_channel ", ") c.Class.implements
      end;
    if [] <> c.Class.inherits then
      begin
	output_string out_channel "\ninherits ";
	separated_list pretty_print_inherits
	  (function () -> output_string out_channel ", ") c.Class.inherits 
      end ;
    do_indent 0;
    output_string out_channel "begin";
    if [] <> c.Class.attributes then
      begin
	do_indent 1 ;
	pretty_print_vardecls 1 "var " "" "\n" c.Class.attributes;
	output_string out_channel "\n";
      end;
    if [] <> c.Class.with_defs then
      begin
	List.iter (pretty_print_with) c.Class.with_defs ;
      end ;
    if [] = c.Class.attributes && [] = c.Class.with_defs then
      output_string out_channel "\n";
    output_string out_channel "end"
  and pretty_print_inherits (inh, args) =
    output_string out_channel inh;
    if args <> [] then
      begin
	output_string out_channel "(";
	separated_list pretty_print_expression
	  (function () -> output_string out_channel ", ") args;
	output_string out_channel ")"
      end
  and pretty_print_with w =
    let indent = if w.With.co_interface = None then 1 else 2
    in
      begin
	match w.With.co_interface with
	    None -> ()
	  | Some c ->
	      do_indent 1;
	      output_string out_channel ("with " ^ c);
      end ;
      do_indent indent;
      pretty_print_methods indent w.With.methods
	(* XXX: Take care of invariants later *)
  and pretty_print_methods indent list =
    separated_list
      (pretty_print_method (indent + 1))
      (function () -> do_indent indent)
      list
  and pretty_print_method indent m =
    output_string out_channel ("op " ^ m.Method.meth_name);
    if m.Method.meth_inpars <> [] || m.Method.meth_outpars <> [] then
      output_string out_channel "(";
    begin
      match (m.Method.meth_inpars, m.Method.meth_outpars) with
	  ([], []) -> ()
	| (i, []) ->
	    output_string out_channel "in ";
	    pretty_print_vardecls 0 "" ", " "" i
	| ([], o) ->
	    output_string out_channel "out ";
	    pretty_print_vardecls 0 "" ", " "" o
	| (i, o) -> 
	    output_string out_channel "in ";
	    pretty_print_vardecls 0 "" ", " "" i;
	    output_string out_channel "; out ";
	    pretty_print_vardecls 0 "" ", " "" o
    end;
    if m.Method.meth_inpars <> [] || m.Method.meth_outpars <> [] then
      output_string out_channel ")";
    (match m.Method.meth_body with
	None -> ()
      | Some s ->
	  output_string out_channel " == " ;
	  do_indent indent;
	  separated_list
	    (function v ->
	      output_string out_channel "var " ;
	      pretty_print_vardecl v)
	    (function () ->
	      output_string out_channel ";" ;
	      do_indent indent)
	    m.Method.meth_vars;
	  if [] <> m.Method.meth_vars then
	    begin
	      output_string out_channel ";" ;
	      do_indent indent
	    end ;
	  pretty_print_statement indent s);
    output_string out_channel "\n"
  and pretty_print_vardecls lvl p d s list =
    separated_list
      (function v ->
	output_string out_channel p;
	pretty_print_vardecl v)
      (function () ->
	output_string out_channel d;
	if lvl > 0 then do_indent lvl)
      list
  and pretty_print_vardecl v =
    output_string out_channel (v.VarDecl.name ^ ": " ^ (Type.as_string v.VarDecl.var_type ));
    ( match v.VarDecl.init with
	Some e -> output_string out_channel " := " ;
	  pretty_print_expression e
      | None -> () )
  and pretty_print_statement lvl statement =
    (** Pretty-print statements and write the code to out. *)
    let open_block prec op_prec =
      if prec < op_prec then output_string out_channel "begin "
    and close_block prec op_prec =
      if prec < op_prec then output_string out_channel " end"
    in
    let rec print lvl prec =
      function
	  Statement.Skip _ -> output_string out_channel "skip";
	| Statement.Assert (_, e) ->
	    output_string out_channel "assert " ; pretty_print_expression e
	| Statement.Assign (_, i, e) ->
	    pretty_print_lhs_list i;
	    output_string out_channel " := ";
	    pretty_print_expression_list e
	| Statement.Await (_, e) -> 
	    output_string out_channel "await ";
	    pretty_print_expression e;
	| Statement.Release _ -> output_string out_channel "release";
	| Statement.AsyncCall (_, l, c, m, a) ->
	    (match l with
		None -> ()
	      | Some l -> pretty_print_lhs l ) ;
	    output_string out_channel "!";
	    pretty_print_expression c ;
	    output_string out_channel ("." ^ m ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel ")"
	| Statement.Reply (_, l, o) ->
	    pretty_print_expression l ;
	    output_string out_channel "?(";
	    pretty_print_lhs_list o;
	    output_string out_channel ")";
	| Statement.Free(_, l) ->
	    output_string out_channel "/* free(" ;
	    pretty_print_expression_list l ;
	    output_string out_channel ") */"
	| Statement.SyncCall (_, c, m, a, r) ->
	    pretty_print_expression c ;
	    output_string out_channel ("." ^ m ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list r;
	    output_string out_channel ")"
	| Statement.AwaitSyncCall (_, c, m, a, r) ->
	    output_string out_channel "await " ;
	    pretty_print_expression c ;
	    output_string out_channel ("." ^ m ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list r;
	    output_string out_channel ")"
	| Statement.LocalAsyncCall (_, l, m, lb, ub, i) ->
	      (match l with
		  None -> ()
		| Some n -> pretty_print_lhs n ) ;
	    output_string out_channel "!" ;
	    output_string out_channel m ;
	    (match lb with
		None -> ()
	      | Some n -> output_string out_channel (":>" ^ n));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<:" ^ n));
	    output_string out_channel "(" ;
	    pretty_print_expression_list i;
	    output_string out_channel ")"
	| Statement.LocalSyncCall (_, m, lb, ub, i, o) ->
	    output_string out_channel m;
	    (match lb with
		None -> ()
	      | Some n -> output_string out_channel (":>" ^ n));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<:" ^ n));
	    output_string out_channel "(" ;
	    pretty_print_expression_list i;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list o;
	    output_string out_channel ")"
	| Statement.AwaitLocalSyncCall (_, m, lb, ub, i, o) ->
	    output_string out_channel ("await " ^ m) ;
	    (match lb with
		None -> ()
	      | Some n -> output_string out_channel (":>" ^ n));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<:" ^ n));
	    output_string out_channel "(" ;
	    pretty_print_expression_list i;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list o;
	    output_string out_channel ")"
	| Statement.Tailcall (_, m, l, u, i) -> assert false
	| Statement.If (_, c, t, f) ->
	    output_string out_channel "if ";
	    pretty_print_expression c;
	    output_string out_channel " then";
	    do_indent (lvl + 1);
	    print (lvl + 1) 25 t;
	    do_indent lvl;
	    output_string out_channel "else";
	    do_indent (lvl + 1);
	    print (lvl + 1) 25 f;
	    do_indent lvl;
	    output_string out_channel "end"
	| Statement.While (_, c, i, b) ->
	    (* The text generated in this branch does not parse in standard
	       Creol.  This should not be changed.  Consult the manual for
	       the reasons. *)
	    output_string out_channel "while ";
	    pretty_print_expression c;
	    (match i with
		None -> ()
	      | Some inv -> 
		  do_indent lvl;
		  output_string out_channel "inv ";
		  pretty_print_expression inv ;
		  do_indent lvl) ;
	    output_string out_channel " do ";
	    do_indent (lvl + 1);
	    print (lvl + 1) 25 b;
	    output_string out_channel " end";
	    do_indent lvl
	| Statement.Sequence (_, s1, s2) -> 
	    let op_prec = 25 in
	    let nl = lvl + if prec < op_prec then 1 else 0 in
	      open_block prec op_prec;
	      print nl op_prec s1;
	      output_string out_channel "; ";
	      do_indent nl;
	      print nl op_prec s2;
	      close_block prec op_prec
	| Statement.Merge (_, l, r) ->
	    let op_prec = 29 in
	    let nl = lvl + if prec < op_prec then 1 else 0 in
	      open_block prec op_prec;
	      print nl op_prec l;
	      output_string out_channel " ||| ";
	      do_indent nl;
	      print nl op_prec r;
	      close_block prec op_prec
	| Statement.Choice (_, l, r) -> 
	    let op_prec = 27 in
	    let nl = lvl + if prec < op_prec then 1 else 0 in
	      open_block prec op_prec;
	      print nl op_prec l;
	      output_string out_channel " [] ";
	      do_indent nl;
	      print nl op_prec r;
	      close_block prec op_prec
	| Statement.Extern (_, s) ->
	    output_string out_channel ("extern \"" ^ s ^ "\"")
    in
      print lvl 25 statement
  and pretty_print_expression exp =
    let open_paren prec op_prec =
      if prec < op_prec then output_string out_channel "("
    and close_paren prec op_prec =
      if prec < op_prec then output_string out_channel ")"
    in
    let rec print prec =
      function
	  Expression.Nil _ -> output_string out_channel "nil"
	| Expression.Null _ -> output_string out_channel "null"
	| Expression.Int (_, i) -> output_string out_channel (string_of_int i)
	| Expression.Float (_, f) ->
	    output_string out_channel (string_of_float f)
	| Expression.Bool (_, b) ->
	    output_string out_channel (string_of_bool b)
	| Expression.String (_, s) ->
	    output_string out_channel ("\"" ^ s ^ "\"")
	| Expression.Id (_, i) -> output_string out_channel i
	| Expression.StaticAttr (_, a, c) ->
	    output_string out_channel (a ^ "@" ^ (Type.as_string c))
	| Expression.Tuple (_, a) ->
	    output_string out_channel "(";
	    pretty_print_expression_list a;
	    output_string out_channel ")";
	| Expression.ListLit (_, a) ->
	    output_string out_channel "[";
	    pretty_print_expression_list a;
	    output_string out_channel "]";
	| Expression.SetLit (_, a) ->
	    output_string out_channel "{";
	    pretty_print_expression_list a;
	    output_string out_channel "}";
	| Expression.FieldAccess(_, e, f) ->
	    print 15 e; output_string out_channel ("`" ^ f)
	| Expression.Unary (_, o, e) ->
	    output_string out_channel (Expression.string_of_unaryop o ^ " ");
	    print (Expression.prec_of_unaryop o) e
	| Expression.Binary (_, o, l, r) ->
	    let lp = fst (Expression.prec_of_binaryop o)
	    and rp = snd (Expression.prec_of_binaryop o)
	    in
      	      open_paren prec lp; print lp l ;
	      output_string out_channel
		(" " ^ (Expression.string_of_binaryop o) ^ " ") ;
	      print rp r; close_paren prec rp
	| Expression.FuncCall (_, i, a) ->
	    output_string out_channel (i ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel ")";
	| Expression.Label (_, l) -> print 121 l; output_string out_channel "?"
	| Expression.If (_, c, t, f) ->
	    output_string out_channel "if "; print 121 c ;
	    output_string out_channel " then "; print 121 t ;
	    output_string out_channel " else "; print 121 f ;
	    output_string out_channel " end";
	| Expression.New (_, t, a) ->
            output_string out_channel ("new " ^ (Type.as_string t) ^ "(");
	    pretty_print_expression_list a ;
	    output_string out_channel ")"
        | Expression.Extern (_, s) ->
            output_string out_channel ("extern \"" ^ s ^ "\"");
	| Expression.SSAId (_, v, n) ->
	    output_string out_channel ("$" ^ v ^ "<" ^ (string_of_int n) ^ ">")
	| Expression.Phi (_, l) ->
	    output_string out_channel "$Phi(" ;
	    pretty_print_expression_list l ;
	    output_string out_channel ")";
    in
      print 121 exp
  and pretty_print_expression_list l =
    separated_list pretty_print_expression
      (function () -> output_string out_channel ", ") l
  and pretty_print_lhs =
      function
	  Expression.LhsVar (_, n) -> output_string out_channel n
	| Expression.LhsAttr(_, n, c) -> output_string out_channel
	    (n ^ "@" ^ (Type.as_string c))
	| Expression.LhsWildcard (_, None) -> output_string out_channel "_"
	| Expression.LhsWildcard (_, Some t) ->
	    output_string out_channel ("_: " ^ (Type.as_string t))
	| Expression.LhsSSAId (_, v, n) ->
	    output_string out_channel ("$" ^ v ^ "<" ^ (string_of_int n) ^ ">")
  and pretty_print_lhs_list l =
    separated_list pretty_print_lhs
      (function () -> output_string out_channel ", ") l
  and do_indent lvl =
    output_string out_channel ("\n" ^ (String.make (lvl * 2) ' '))
  in
    separated_list pretty_print_declaration
      (function () -> output_string out_channel "\n\n") input ;
    output_string out_channel "\n";
    flush out_channel
