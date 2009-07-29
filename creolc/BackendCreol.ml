(*
 * BackendCreol.ml -- Emit a tree as a Creol source file.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007, 2008 by Marcel Kyas
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
 * along with this program.   If not, see <http://www.gnu.org/licenses/>.
 *)

(*s Emit a tree as a Creol program. *)

open Misc
open Creol
open Format

(* These passes are required by this backend. *)

let requires _ = []

(* These passes must not be enabled for this backend. *)

let conflicts _ = ["expand"]

(** The indentiation level to use. *)
let indent_level = 2


let print_comma () = print_string "," ; print_space ()


let print_semi () = print_string ";" ; print_space ()


let rec print_expression exp =
  let open_paren prec op_prec =
    if prec < op_prec then begin open_box 0 ; print_string "(" end
  and close_paren prec op_prec =
    if prec < op_prec then begin print_string ")" ; close_box () end
  in
  let rec print prec =
    function
	Expression.This _ ->
	  print_string "this"
      | Expression.QualifiedThis (_, t) ->
	  print_string ("this as " ^ (Type.string_of_type t))
      | Expression.Caller _ ->
	  print_string "caller"
      | Expression.Now _ ->
	  print_string "now"
      | Expression.Nil _ ->
	  print_string "nil"
      | Expression.Null _ ->
	  print_string "null"
      | Expression.History _ ->
	  print_string "history"
      | Expression.Int (_, i) ->
          print_string (Big_int.string_of_big_int i)
      | Expression.Float (_, f) ->
	  print_float f
      | Expression.Bool (_, b) ->
	  print_string (string_of_bool b)
      | Expression.String (_, s) ->
	  print_string ("\"" ^ s ^ "\"")
      | Expression.Id (_, i) ->
	  print_string i
      | Expression.StaticAttr (_, a, c) ->
	  print_string (a ^ "@" ^ (Type.string_of_type c))
      | Expression.Tuple (_, a) ->
	  print_string "(";
	  print_expression_list a;
	  print_string ")"
      | Expression.ListLit (_, a) ->
	  print_string "[";
	  print_expression_list a ;
	  print_string "]"
      | Expression.SetLit (_, a) ->
	  print_string "{";
	  print_expression_list a;
	  print_string "}";
      | Expression.MapLit (_, a) ->
	  print_string "{|";
	  print_binding_list a;
	  print_string "|}";
      | Expression.FuncCall (_, o, [e]) when Expression.unaryop_p o ->
	  print_string o ;
	  print_space () ;
	  print (Expression.prec_of_unaryop o) e
      | Expression.FuncCall (_, o, [l; r]) when Expression.binaryop_p o ->
	  let (lp, rp) = Expression.prec_of_binaryop o in
      	    open_paren prec lp;
	    print lp l ;
	    print_space () ;
	    print_string o ;
	    print_space () ;
	    print rp r;
	    close_paren prec rp
      | Expression.FuncCall (_, i, a) ->
	  print_string (i ^ "(") ;
	  print_expression_list a ;
	  print_string ")"
      | Expression.Label (_, l) ->
	  print 121 l;
	  print_string "?"
      | Expression.If (_, c, t, f) ->
	  print_string "if" ;
	  print_space () ;
	  print 121 c ;
	  print_space () ;
	  print_string "then" ;
	  print_space () ;
	  print 121 t ;
	  print_space () ;
	  print_string "else" ;
	  print_space () ;
	  print 121 f ;
	  print_space () ;
	  print_string "end";
      | Expression.New (_, t, a) ->
          print_string ("new " ^ (Type.string_of_type t) ^ "(");
	  print_expression_list a ;
	  print_string ")"
      | Expression.Choose (_,v, t, e) ->
	  print_string ("(some " ^ v ^ ": " ^ (Type.string_of_type t)) ;
	  print_expression e ;
	  print_string ")"
      | Expression.Exists (_,v, t, e) ->
	  print_string ("(exists " ^ v ^ ": " ^ (Type.string_of_type t)) ;
	  print_expression e ;
	  print_string ")"
      | Expression.Forall (_,v, t, e) ->
	  print_string ("(forall " ^ v ^ ": " ^ (Type.string_of_type t)) ;
	  print_expression e ;
	  print_string ")"
      | Expression.Extern (_, s) ->
          open_hbox () ;
	  print_string "external" ;
	  print_space () ;
	  print_string ("\"" ^ s ^ "\"") ;
	  close_box ()
      | Expression.ObjLit (_, s) ->
	  print_string ("object " ^ s)
      | Expression.LabelLit (_, e) ->
	  print_string "label(" ;
	  print_expression_list e ;
	  print_string ")"
      | Expression.SSAId (_, v, n) ->
	  print_string ("$" ^ v ^ "<" ^ (string_of_int n) ^ ">")
      | Expression.Phi (_, l) ->
	  print_string "$Phi(" ;
	  print_expression_list l ;
	  print_string ")";
  in
    open_box 2 ;
    print 121 exp ;
    close_box ()
and print_expression_list l =
  separated_list print_expression print_comma l
and print_binding_list l =
  separated_list print_binding print_comma l
and print_binding (d, r) =
  open_box 2 ;
  print_expression d ;
  print_space () ;
  print_string "|->" ;
  print_space () ;
  print_expression r ;
  close_box ()


let pretty_print_expression out_channel expr =
  let () = set_formatter_out_channel out_channel in
    open_box 2 ;
    print_expression expr ;
    close_box () ;
    print_newline ()


let print_lhs =
  function
      Expression.LhsId (_, n) ->
	print_string n
    | Expression.LhsAttr(_, n, c) ->
	print_string (n ^ "@" ^ (Type.string_of_type c))
    | Expression.LhsWildcard (_, None) ->
	print_string "_"
    | Expression.LhsWildcard (_, Some t) ->
	print_string ("_: " ^ (Type.string_of_type t))
    | Expression.LhsSSAId (_, v, n) ->
	print_string ("$" ^ v ^ "<" ^ (string_of_int n) ^ ">")


let print_lhs_list l = separated_list print_lhs print_comma l


let rec print_statement statement =
  (** Pretty-print statements and write the code to out. *)
  let open_block prec op_prec =
    if prec < op_prec then
      begin open_vbox 2 ; print_string "begin" ; print_space () end
  and close_block prec op_prec =
    if prec < op_prec then
      begin print_space () ; print_string "end" ; close_box () end
  in
  let rec print (prec : int) : Statement.t -> unit =
    function
	Statement.Skip _ ->
	  open_box 2 ; print_string "skip" ; close_box ()
      | Statement.Assert (_, e) ->
	  open_box 2 ; print_string "assert" ; print_space () ;
	  print_expression e ; close_box ()
      | Statement.Prove (_, e) ->
	  open_box 2 ; print_string "prove" ; print_space () ;
	  print_expression e ; close_box ()
      | Statement.Assign (_, i, e) ->
	  open_box 2 ; print_lhs_list i;
	  print_space () ; print_string ":=" ; print_space () ;
	  print_expression_list e ; close_box ()
      | Statement.Await (_, e) -> 
	  open_box 2 ; print_string "await"; print_space () ;
	  print_expression e ; close_box ()
      | Statement.Posit (_, e) -> 
	  open_box 2 ; print_string "posit"; print_space () ;
	  print_expression e ; close_box ()
      | Statement.Release _ ->
	  open_box 2 ; print_string "release" ; close_box ()
      | Statement.AsyncCall (_, l, c, m, (s,_,_), a) ->
	  open_box 2 ;
	  (match l with
	       None -> ()
	     | Some l -> print_lhs l ) ;
	  print_string "!";
	  print_expression c ;
	  print_string ("." ^ m ^ "(");
	  print_expression_list a;
	  print_string ")" ;
	  print_space () ;
          begin
	    match s with
	        None -> ()
	      | Some t ->
	          print_space () ;
	          print_string "as";
	          print_space () ;
	          print_string (Type.string_of_type t)
	  end ;
	  close_box ()
      | Statement.Get (_, l, o) ->
	  open_box 2 ;
	  print_expression l ;
	  print_string "?(" ;
	  print_lhs_list o ;
	  print_string ")" ;
	  close_box ()
      | Statement.Free (_, l) ->
	  open_box 2 ;
	  print_string "/* free(" ;
	  print_lhs_list l ;
	  print_string ") */" ;
	  close_box ()
      | Statement.Bury (_, l) ->
	  open_box 2 ;
	  print_string "/* bury(" ;
	  print_lhs_list l ;
	  print_string ") */" ;
	  close_box ()
      | Statement.SyncCall (_, c, m, (s, _, _), a, r) ->
	  open_box 2 ;
	  print_expression c ;
	  print_string ("." ^ m ^ "(") ;
	  print_expression_list a ;
	  print_semi () ;
	  print_lhs_list r ;
	  print_string ")" ;
          begin
	    match s with
	        None -> ()
	      | Some t ->
	          print_space () ;
	          print_string "as";
	          print_space () ;
	          print_string (Type.string_of_type t)
	  end ;
	  close_box ()
      | Statement.AwaitSyncCall (_, c, m, (s, _, _), a, r) ->
	  open_box 2 ;
	  print_string "await" ;
	  print_space () ;
	  print_expression c ;
	  print_string ("." ^ m ^ "(");
	  print_expression_list a;
	  print_string "; " ;
	  print_lhs_list r;
	  print_string ")" ;
          begin
	    match s with
	        None -> ()
	      | Some t ->
	          print_space () ;
	          print_string "as";
	          print_space () ;
	          print_string (Type.string_of_type t)
	  end ;
	  close_box ()
      | Statement.LocalAsyncCall (_, l, m, _, lb, ub, i) ->
	  open_box 2 ;
	  begin
	    match l with
		None -> ()
	      | Some n -> print_lhs n 
	  end ;
	  print_string "!" ;
	  print_string m ;
	  begin
	    match lb with
		None -> ()
	      | Some n -> print_string (":>" ^ n)
	  end ;
	  begin
	    match ub with
		None -> ()
	      | Some n -> print_string ("<:" ^ n)
	  end ;
	  print_string "(" ;
	  print_expression_list i ;
	  print_string ")" ;
	  close_box ()
      | Statement.LocalSyncCall (_, m, _, lb, ub, i, o) ->
	  open_box 2 ;
	  print_string m ;
	  (match lb with
	       None -> ()
	     | Some n -> print_string (":>" ^ n));
	  (match ub with
	       None -> ()
	     | Some n -> print_string ("<:" ^ n));
	  print_string "(" ;
	  print_expression_list i;
	  print_semi () ;
	  print_lhs_list o;
	  print_string ")" ;
	  close_box ()
      | Statement.AwaitLocalSyncCall (_, m, _, lb, ub, i, o) ->
	  open_box 2 ;
	  print_string "await" ;
	  print_space () ;
	  print_string m ;
	  (match lb with
	       None -> ()
	     | Some n -> print_string (":>" ^ n));
	  (match ub with
	       None -> ()
	     | Some n -> print_string ("<:" ^ n));
	  print_string "(" ;
	  print_expression_list i;
	  print_semi () ;
	  print_lhs_list o ;
	  print_string ")" ;
	  close_box ()
      | Statement.MultiCast (_, c, m, _, a) ->
	  open_box 2 ;
	  print_string "!";
	  print_expression c ;
	  print_string ("." ^ m ^ "(") ;
	  print_expression_list a ;
	  print_string ")" ;
	  close_box ()
      | Statement.Tailcall (_, c, m, _, i) ->
	  open_box 2 ;
	  print_string "/* tailcall " ;
	  print_expression c ;
	  print_string ("." ^ m ^ "(");
	  print_expression_list i ;
	  print_string ") */" ;
	  close_box ()
      | Statement.StaticTail (_, m, _, l, u, i) ->
	  open_box 2 ;
	  print_string "/* static tailcall " ;
	  print_string m ;
	  (match l with
	       None -> ()
	     | Some n -> print_string (":>" ^ n));
	  (match u with
	       None -> ()
	     | Some n -> print_string ("<:" ^ n));
	  print_string "(" ;
	  print_expression_list i;
	  print_string ") */" ;
	  close_box ()
      | Statement.Return (_, o) ->
	  open_hbox () ;
	  print_string "/* return(" ;
	  print_expression_list o ;
	  print_string ") */" ;
	  close_box ()
      | Statement.If (_, c, t, f) ->
	  open_box 2 ;
	  print_string "if" ;
	  print_space () ;
	  begin
	    open_hbox () ;
	    print_expression c;
	    close_box ()
	  end ;
	  print_space () ;
	  print_string "then";
	  print_space () ;
	  begin
	    open_vbox 2 ;
	    print 25 t ;
	    close_box ()
	  end ;
	  print_space () ;
	  print_string "else";
	  print_space () ;
	  begin
	    open_vbox 2 ;
	    print 25 f ;
	    close_box ()
	  end ;
          print_space () ;
	  print_string "end" ;
	  close_box ()
      | Statement.While (_, c, i, b) ->
	  (* The text generated in this branch does not parse in standard
	     Creol.  This should not be changed.  Consult the manual for
	     the reasons. *)
	  open_hbox () ;
          print_string "while";
          print_space () ;
	  print_expression c;
	  begin
            match i with
	      | Expression.Bool (_, true) -> ()
	      | _ -> 
		  print_string "inv" ;
		  print_space () ;
		  print_expression i ;
          end ;
	  print_space () ;
	  print_string "do" ;
          close_box () ;
          print_break 2 2 ;
	  open_vbox 0 ;
	  print 25 b ;
	  close_box () ;
          print_space () ;
	  print_string "end";
      | Statement.DoWhile (_, c, i, b) ->
	  (* The text generated in this branch does not parse in standard
	     Creol.  This should not be changed.  Consult the manual for
	     the reasons. *)
	  print_string "do" ; print_space () ;
	  open_box 2 ;
	  print 25 b ;
	  close_box () ;
	  (match i with
	       Expression.Bool (_, true) -> ()
	     | _ -> 
		 open_box 2 ;
		 print_string "inv" ;
		 print_space () ;
		 print_expression i ;
		 close_box ()) ;
	  print_string "while" ;
	  print_space () ;
	  print_expression c
      | Statement.Sequence (_, s1, s2) -> 
	  let op_prec = 25 in
	    open_block prec op_prec ;
	    print op_prec s1 ;
	    print_semi () ;
	    print op_prec s2 ;
	    close_block prec op_prec
      | Statement.Merge (_, s1, s2) ->
	  let op_prec = 29 in
	    open_block prec op_prec ;
	    print op_prec s1 ;
	    print_space () ;
	    print_string "|||" ;
	    print_space () ;
	    print op_prec s2 ;
	    close_block prec op_prec
      | Statement.Choice (_, s1, s2) -> 
	  let op_prec = 27 in
	    open_block prec op_prec;
	    print op_prec s1 ;
	    print_space () ;
	    print_string "[]" ;
	    print_space () ;
	    print op_prec s2 ;
	    close_block prec op_prec
      | Statement.Continue (_, e) ->
          open_hbox () ;
	  print_string "/* continue " ;
	  print_expression e ;
	  print_string "*/" ;
	  close_box ()
      | Statement.Extern (_, s) ->
	  open_hbox () ;
	  print_string "external" ;
	  print_space () ;
	  print_string ("\"" ^ s ^ "\"") ;
	  close_box ()
  in
    print 25 statement


let pretty_print_statement out_channel stmt =
  let () = set_formatter_out_channel out_channel in
    open_vbox 2 ;
    print_statement stmt ;
    close_box () ;
    print_newline ()


let pretty_print_program out_channel input =
  (** Write a pretty-printed tree to [out_channel].
      
      The result of [lower] cannot be printed to a valid creol
      program.  The pretty-printed result can, however, be used for
      debugging. *)
  let rec print_declaration =
    function
	Declaration.Class c when not (Class.hidden_p c) ->
	  print_class c ; print_space () ; print_space ()
      | Declaration.Interface i when not (Interface.hidden_p i) ->
	  print_iface i ; print_space () ; print_space ()
      | Declaration.Object o when not (Object.hidden_p o) ->
	  print_object o ; print_space () ; print_space ()
      | Declaration.Exception e when not (Exception.hidden_p e) ->
	  print_exception e ; print_space () ; print_space ()
      | Declaration.Datatype d when not (Datatype.hidden_p d) ->
          print_datatype d ; print_space () ; print_space ()
      | Declaration.Function f when not (Function.hidden_p f) ->
	  print_function f ; print_space () ; print_space ()
      | Declaration.Future f ->
	  print_future f ; print_space () ; print_space ()
      | Declaration.NewClass c ->
	  print_new_class c ; print_space () ; print_space ()
      | Declaration.Retract r -> 
	  print_retract r ; print_space () ; print_space ()
      | Declaration.Update u -> 
	  print_update u ; print_space () ; print_space ()
      | _ -> ()
  and print_function f =
    open_box 2 ;
    print_string "function" ;
    print_space () ;
    print_string f.Function.name ;
    print_string "(" ;
    print_vardecls "" print_comma f.Function.parameters ;
    print_string ")" ;
    print_string ":" ;
    print_space () ;
    print_string (Type.string_of_type f.Function.result_type) ;
    print_space () ;
    print_string "==" ;
    print_space () ;
    open_box 2 ;
    print_expression f.Function.body ;
    close_box () ;
    close_box ()
  and print_datatype d =
    open_box 2 ;
    print_string "datatype" ;
    print_space () ;
    print_string (Type.string_of_type d.Datatype.name) ;
    if d.Datatype.supers <> [] then
      begin
	print_space () ;
        print_string "from" ;
	print_space () ;
	separated_list (function t -> print_string (Type.string_of_type t))
	  print_comma
	  d.Datatype.supers
      end ;
      close_box ()
  and print_exception e =
    open_box 2 ;
    print_string "exception" ;
    print_space () ;
    print_string e.Exception.name ;
    begin
      match e.Exception.parameters with
          [] -> ()
	| l -> print_string "(";
	    print_vardecls "" print_comma l;
	    print_string ")" 
    end ;
    close_box ()
  and print_object obj =
    open_vbox 0 ;
    print_expression obj.Object.name ;
    print_string (" : " ^ (Type.string_of_type obj.Object.cls)) ;
    print_space () ;
    print_string "begin" ;
    print_space () ;
    open_hbox () ;
    print_space () ;
    print_space () ;
    close_box () ;
    open_vbox 0 ;
    if [] <> obj.Object.attributes then
	print_vardecls "var " print_space obj.Object.attributes ;
    print_space () ;
    print_string "Active Process:" ;
    print_space () ;
    open_hbox () ;
    print_space () ;
    print_space () ;
    close_box () ;
    open_vbox 0 ;
    print_process obj.Object.process ;
    close_box () ;
    print_space () ;
    if [] <> obj.Object.process_queue then
      begin
	print_string "Process Queue:" ;
        print_space () ;
        open_hbox () ;
        print_space () ;
        print_space () ;
        close_box () ;
        open_vbox 0;
	separated_list print_process print_space obj.Object.process_queue ;
        close_box ()
      end ;
    close_box () ;
    print_space () ;
    print_string "end" ;
    close_box ()
  and print_process =
    function 
      | { Process.attributes = []; code = (Statement.Skip _) } ->
        open_hbox () ; print_string "idle" ; close_box ()
      | { Process.attributes = []; code = c } ->
	print_statement c ;
        print_space ()
      | { Process.attributes = a; code = c } ->
	print_vardecls "var " print_space a;
        print_space () ;
	print_statement c;
        print_space ()
  and print_future f =
    open_box 2 ;
    print_string "Future" ;
    print_space () ;
    print_expression f.Future.name ;
    print_space () ;
    print_string "with" ;
    print_space () ;
    print_string (Big_int.string_of_big_int f.Future.references) ;
    print_space () ;
    print_string "references" ;
    print_space () ;
    print_string "is" ;
    print_space () ;
    if f.Future.completed then
      print_expression_list f.Future.value
    else
      print_string "Pending" ;
    close_box ()
  and print_iface i =
    open_vbox 0 ;
    begin
      open_hbox () ;
      print_string "interface" ;
      print_space () ;
      print_string i.Interface.name ;
      close_box ()
    end ;
    if [] <> i.Interface.inherits then
      begin
	open_box 2 ;
	print_space () ;
	print_string "inherits ";
	separated_list print_inherits print_comma i.Interface.inherits ;
	close_box () 
      end ;
    if [] <> i.Interface.pragmas then
      begin
	open_box 2 ;
	print_space () ;
	print_string "pragma " ;
	separated_list print_pragma print_comma i.Interface.pragmas ;
	close_box () 
      end ;
    print_space () ;
    print_string "begin";
    print_break 2 0 ;
    if [] <> i.Interface.with_decls then
      begin
        open_vbox 0 ;
	separated_list print_with print_space i.Interface.with_decls ;
        close_box () ;
      end ;
    print_space () ;
    print_string "end" ;
    close_box ()
  and print_class c =
    open_vbox 0 ;
    open_box 2 ;
    print_string "class" ;
    print_space () ;
    print_string c.Class.name ;
    if [] <> c.Class.parameters then
      begin
	print_string "(";
	print_vardecls "" print_comma c.Class.parameters ;
	print_string ")"
      end ;
    close_box () ;
    if [] <> c.Class.implements || [] <> c.Class.contracts ||
       [] <> c.Class.inherits || [] <> c.Class.pragmas 
    then
      begin
        print_space () ;
        open_hbox () ;
        print_space () ;
        print_space () ;
        close_box () ;
        open_vbox 0 ;
        if [] <> c.Class.implements then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "implements " ;
	    separated_list print_inherits print_comma c.Class.implements ;
 	    close_box ()
          end;
        if [] <> c.Class.contracts then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "contracts " ;
	    separated_list print_inherits print_comma c.Class.contracts ;
	    close_box ()
          end;
        if [] <> c.Class.inherits then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "inherits ";
	    separated_list print_inherits print_comma c.Class.inherits ;
	    close_box () 
          end ;
        if [] <> c.Class.pragmas then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "pragma " ;
	    separated_list print_pragma print_comma c.Class.pragmas ;
	    close_box () 
          end ;
        close_box ()
      end ;
    print_space () ;
    print_string "begin" ;
    print_space () ;
    open_hbox () ; print_break 2 2 ; close_box () ;
    open_vbox 0 ;
    if [] <> c.Class.attributes then
      begin
	print_vardecls "var " print_space c.Class.attributes ;
	print_space ()
      end;
    if [] <> c.Class.invariants then
      begin
	separated_list print_inv print_space c.Class.invariants ;
      end;
    if [] <> c.Class.with_defs then
      begin
	separated_list print_with print_space c.Class.with_defs ;
      end ;
    if [] = c.Class.attributes && [] = c.Class.with_defs then print_space () ;
    close_box () ;
    print_space () ;
    print_string "end" ;
    close_box ()
  and print_new_class c =
    let () = print_string "new " in
    let () = print_class c.NewClass.cls in
    let () = print_dependencies c.NewClass.dependencies in
      ()
  and print_retract upd =
    open_vbox 0 ;
    open_hbox () ;
    print_string "retract" ;
    print_space () ;
    print_string upd.Retract.name ;
    close_box () ;
    if [] <> upd.Retract.inherits || [] <> upd.Retract.pragmas 
    then
      begin
        print_space () ;
        open_hbox () ;
        print_space () ;
        print_space () ;
        close_box () ;
        open_vbox 0 ;
        if [] <> upd.Retract.inherits then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "inherits ";
	    separated_list print_inherits print_comma upd.Retract.inherits ;
	    close_box () 
          end ;
        if [] <> upd.Retract.pragmas then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "pragma " ;
	    separated_list print_pragma print_comma upd.Retract.pragmas ;
	    close_box () 
          end ;
        close_box ()
      end ;
    print_space () ;
    print_string "begin" ;
    print_space () ;
    open_hbox () ; print_break 2 2 ; close_box () ;
    open_vbox 0 ;
    if [] <> upd.Retract.attributes then
      begin
	print_vardecls "var " print_space upd.Retract.attributes ;
	print_space ()
      end;
    if [] <> upd.Retract.with_decls then
      begin
	separated_list print_with print_space upd.Retract.with_decls ;
      end ;
    if [] = upd.Retract.attributes && [] = upd.Retract.with_decls then
      print_space () ;
    print_dependencies upd.Retract.dependencies ;
    close_box () ;
    print_space () ;
    print_string "end" ;
    close_box ()
  and print_update upd =
    open_vbox 0 ;
    open_hbox () ;
    print_string "update" ;
    print_space () ;
    print_string upd.Update.name ;
    close_box () ;
    if [] <> upd.Update.implements || [] <> upd.Update.contracts ||
       [] <> upd.Update.inherits || [] <> upd.Update.pragmas 
    then
      begin
        print_space () ;
        open_hbox () ;
        print_space () ;
        print_space () ;
        close_box () ;
        open_vbox 0 ;
        if [] <> upd.Update.implements then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "implements " ;
	    separated_list print_inherits print_comma upd.Update.implements ;
 	    close_box ()
          end;
        if [] <> upd.Update.contracts then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "contracts " ;
	    separated_list print_inherits print_comma upd.Update.contracts ;
	    close_box ()
          end;
        if [] <> upd.Update.inherits then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "inherits ";
	    separated_list print_inherits print_comma upd.Update.inherits ;
	    close_box () 
          end ;
        if [] <> upd.Update.pragmas then
          begin
	    open_box 2 ;
	    print_space () ;
	    print_string "pragma " ;
	    separated_list print_pragma print_comma upd.Update.pragmas ;
	    close_box () 
          end ;
        close_box ()
      end ;
    print_space () ;
    print_string "begin" ;
    print_space () ;
    open_hbox () ; print_break 2 2 ; close_box () ;
    open_vbox 0 ;
    if [] <> upd.Update.attributes then
      begin
	print_vardecls "var " print_space upd.Update.attributes ;
	print_space ()
      end;
    if [] <> upd.Update.with_defs then
      begin
	separated_list print_with print_space upd.Update.with_defs ;
      end ;
    if [] = upd.Update.attributes && [] = upd.Update.with_defs then
      print_space () ;
    print_dependencies upd.Update.dependencies ;
    close_box () ;
    print_space () ;
    print_string "end" ;
    close_box ()      
  and print_dependencies deps =
    ()
  and print_inherits inh =
    print_string inh.Inherits.name ;
    if inh.Inherits.arguments <> [] then
      begin
	print_string "(";
	separated_list print_expression print_comma inh.Inherits.arguments ;
	print_string ")"
      end
  and print_with w =
    begin
      match w.With.co_interface with
        | Type.Internal -> ()
        | t ->
	    open_hbox () ;
	    print_string "with" ;
	    print_space () ; 
	    print_string (Type.string_of_type t) ;
	    close_box () ;
	    print_space () ;
            open_hbox () ; print_break 2 0 ; close_box () ;
    end ;
    open_vbox 0 ;
    separated_list print_method print_space w.With.methods ;
    separated_list print_inv print_space w.With.invariants ;
    close_box ()
  and print_inv e =
    open_box 2 ; print_string "inv " ; print_expression e ; close_box ()
  and print_method m =
    begin
      open_vbox 4 ;
      open_box 2 ;
      print_string "op" ;
      print_space () ;
      print_string m.Method.name;
      begin
        match (m.Method.inpars, m.Method.outpars) with
	    ([], []) -> ()
	  | (i, []) ->
              print_string "(";
	      print_string "in" ;
	      print_space () ;
	      print_vardecls "" print_comma i ;
              print_string ")"
	  | ([], o) ->
              print_string "(";
	      print_string "out";
	      print_space () ;
	      print_vardecls "" print_comma o ;
              print_string ")"
	  | (i, o) -> 
              print_string "(";
	      print_string "in" ;
	      print_space () ;
	      print_vardecls "" print_comma i ;
	      print_semi () ;
	      print_string "out" ;
	      print_space () ;
	      print_vardecls "" print_comma o ;
              print_string ")"
      end ;
      match m.Method.body with
	| None -> 
	    close_box ()
        | Some stmt ->
	    print_space () ;
	    print_string "==" ;
            close_box () ;
            print_space () ;
	    open_vbox 0 ;
	    if [] <> m.Method.vars then
	      begin
	        print_vardecls "var " print_semi m.Method.vars ; print_semi ()
              end ;
	    print_statement stmt ;
	    close_box ()
    end ;
    close_box ()
  and print_vardecls prefix delimiter vardecls =
    let print vardecl =
      print_string prefix; print_vardecl vardecl
    in
      separated_list print delimiter vardecls
  and print_vardecl v =
    open_box 2 ;
    print_string v.VarDecl.name ;
    print_string ":" ;
    print_space () ;
    print_string (Type.string_of_type v.VarDecl.var_type);
    begin
      match v.VarDecl.init with
        | None -> ()
        | Some e ->
	    print_space () ;
	    print_string ":=" ;
	    print_space () ;
	    print_expression e ;
    end ;
    close_box ()
  and print_pragma { Pragma.name = n; values = v } =
    print_string n ;
    if List.length v > 0 then
      begin
	print_string "(";
	print_expression_list v;
	print_string ")"
      end
  in
    let () = set_formatter_out_channel out_channel in
      open_vbox 0 ;
      separated_list print_declaration (fun () -> ()) input.Program.decls ;
      close_box () ;
      print_newline ()
