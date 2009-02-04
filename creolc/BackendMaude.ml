(*
 * BackendMaude.ml -- Emit a tree to Maude.
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


(** {2 Maude Backend}

    This backend emits maude terms for the different versions of the
    Maude interpreter. *)

open Misc
open Creol
open Format

type target = Interpreter | Modelchecker | Realtime | Updates

type options = {
  mutable target: target;
}

let subtargets =
  [ ("interpreter", "");
    ("modelchecker", "");
    ("realtime", "");
    ("updates", "");
  ]

let subtarget_of_string =
  function
    | "interpreter" -> Interpreter
    | "modelchecker" -> Modelchecker
    | "realtime" -> Realtime
    | "updates" -> Updates

let string_of_subtarget =
  function
    | Interpreter -> "interpreter"
    | Modelchecker -> "modelchecker"
    | Realtime -> "realtime"
    | Updates -> "updates"



let requires =
  function
      { target = Interpreter } ->
	[ "expand"; "free" ]
    | { target = Modelchecker } -> 
	[ "expand"; "free" ; "bury"; "tailcall"]
    | { target = Realtime } ->
	[ "expand"; "free" ]
    | { target = Updates } ->
	[ "expand"; "free" ]

let conflicts =
  function
      { target = Interpreter } ->
	[]
    | { target = Modelchecker } -> 
	[]
    | { target = Realtime } ->
	[]
    | { target = Realtime } ->
	[]

let interpreter =
  function
    | Interpreter -> "creol-interpreter"
    | Modelchecker -> "creol-modelchecker"
    | Realtime -> "creol-realtime"
    | Updates -> "creol-updates"


(** Parse the subtarget features and construct a corresponding option
    structure. *)
let features_of_subtarget s =
  match subtarget_of_string s with
    | Interpreter -> { target = Interpreter }
    | Modelchecker -> { target = Modelchecker }
    | Realtime -> { target = Realtime }
    | Updates -> { target = Updates }

(** Write a Creol program as a maude term. If the program is parsable
    but not semantically correct, this function will only produce
    garbage. *)
let emit subtarget out_channel input =
  let print_comma () = print_string "," ; print_space () in
  let rec of_type =
    function
	Type.Basic n -> print_string n
      | Type.Application (n, _) -> print_string n
      | _ -> assert false
  and of_message_list ?(empty = "emp") ?(separator = "::") =
    let prsep () = print_space () ; print_string separator ; print_space () in
      (** Compile a list of expressions into the Creol Maude Machine. *)
      function
        | [] -> print_string empty
        | l -> separated_list print_string prsep l
  and of_expression =
    function
      | Expression.This _ -> print_string "\"this\""
      | Expression.QualifiedThis _ -> print_string "\"this\""
      | Expression.Caller _ -> print_string "\"caller\""
      | Expression.Null _ -> print_string "null"
      | Expression.Nil _ -> print_string "list(emp)"
      | Expression.Now _ -> print_string "now"
      | Expression.Int (_, i) ->
	  print_string ("int(" ^ (Big_int.string_of_big_int i) ^ ")")
      | Expression.Float (_, f) -> 
	  print_string ("float(" ^ (string_of_float f) ^ ")")
      | Expression.Bool (_, false) -> print_string "bool(false)"
      | Expression.Bool (_, true) -> print_string "bool(true)"
      | Expression.String (_, s) -> print_string ("str(\"" ^ s ^ "\")")
      | Expression.Id (_, i) -> print_string ("\"" ^ i ^ "\"")
      | Expression.StaticAttr (_, a, c) ->
	  print_string ("( \"" ^ a ^ "\" @ \""); of_type c ; print_string "\" )"
      | Expression.Tuple (_, l) | Expression.ListLit (_, l) ->
	  print_string "list(" ; of_expression_list l ; print_string ")"
      | Expression.SetLit (_, l) ->
	  print_string "set(" ;
	  of_expression_list ~empty:"emptyset" ~separator:":" l ;
	  print_string ")" ;
      | Expression.MapLit (_, l) ->
	  print_string "map(" ;
	  of_bindings l ;
	  print_string ")" ;
      | Expression.FuncCall(_, f, a) as e ->
	  let rt = Expression.get_type e
	  and dt = List.map (Expression.get_type) a in
	  let sg = Type.Function (Type.Tuple dt, rt) in
	  let fd =
            Function.external_definition (Program.find_function input f sg)
          in
	    print_string ("\"" ^ fd ^ "\" ( " );
	    of_expression_list a;
	    print_string " )"
      | Expression.Label(_, l) ->
	  print_string "?(" ; of_expression l ; print_string ")"
      | Expression.New (_, c, a) -> assert false
      | Expression.If (_, c, t, f) ->
	  print_string "(if " ;
	  of_expression c ;
	  print_string " th " ;
	  of_expression t ;
	  print_string " el " ;
	  of_expression f ;
	  print_string " fi)"
      | Expression.Extern _ -> assert false
      | Expression.LabelLit (_, label) ->
          print_string "label(" ;
	  of_expression_list label ;
	    (* XXX: Actually broken, but we don't care *)
	  print_string ")"
      | Expression.ObjLit (_, name) ->
          print_string "ob(" ;
	  print_string name ;
	  print_string ")"
      | Expression.SSAId (_, n, v) -> 
	  print_string ("\"" ^ n ^ "\" ***(" ^ (string_of_int v) ^ ")") ;
      | Expression.Phi (_, i::l) ->
	  of_expression i ;
	  print_string " ***( Phi(";
	  of_expression_list (i::l) ;
	  print_string ")"
      | Expression.Phi (_, []) -> assert false
  and of_expression_list ?(empty = "emp") ?(separator = "::") =
    let prsep () = print_space () ; print_string separator ; print_space () in
      (** Compile a list of expressions into the Creol Maude Machine. *)
      function
        | [] -> print_string empty
        | l -> separated_list of_expression prsep l
  and of_bindings ?(separator = ",") =
    let prsep () = print_space () ; print_string separator ; print_space () in
    let of_binding (d, r) =
      open_box 2 ;
      print_string "mapentry(" ;
      of_expression d;
      print_space () ;
      print_string ",";
      print_space () ;
      of_expression r ;
      print_string ")" ;
      close_box ()
    in
      (** Compile a list of expressions into the Creol Maude Machine. *)
      function
        | [] -> print_string "empty"
        | l -> separated_list of_binding prsep l
  and of_lhs =
    function
	Expression.LhsId (_, i) -> print_string ("\"" ^ i ^ "\"")
      | Expression.LhsAttr (_, i, c) ->
	  print_string ("( \"" ^ i ^ "\" @ \"") ;
	  of_type c ;
	  print_string "\" )"
      | Expression.LhsWildcard _ -> print_string "_"
      | Expression.LhsSSAId (_, n, v) -> 
	  print_string ("\"" ^ n ^ "\" ***(" ^ (string_of_int v) ^ ")")
  and of_lhs_list =
    (** Translate a list of left hand side expressions a list of
	Attribute identifiers. *)
    function
	[] -> print_string "noVid"
      | lst -> separated_list of_lhs print_comma lst
  and of_statement stmt =
    let open_paren prec op_prec =
      if prec < op_prec then begin open_box 2 ; print_string "(" end
    and close_paren prec op_prec =
      if prec < op_prec then begin print_string ")" ; close_box () end
    in let rec print prec =
      function
	  Statement.Skip _ ->
	    print_string "skip"
	| Statement.Release _ ->
	    print_string "release"
	| Statement.Await (_, e) ->
	    print_string "await"; print_space () ; of_expression e
	| Statement.Posit (_, e) ->
	    print_string "posit"; print_space () ; of_expression e
	| Statement.Assert (_, e) ->
	    print_string "assert"; print_space () ; of_expression e
	| Statement.Prove (n, _) ->
	    print_string "skip" (* XXX: Find something smarter. *)
	| Statement.Assign (_, [n], [Expression.New (_, c, e)]) ->
	    print_string "new( " ;
	    of_lhs n ;
	    print_string " ; \"" ;
	    of_type c ;
	    print_string "\" ; " ;
	    of_expression_list e ;
	    print_string " )"
	| Statement.Assign (_, i, e) ->
	    print_string "assign( " ;
	    of_lhs_list i;
	    print_string " ; " ;
	    of_expression_list e ;
	    print_string " )" ;
	| Statement.SyncCall _
	| Statement.AwaitSyncCall _
	| Statement.AsyncCall (_, None, _, _, _, _) ->
	    assert false
	| Statement.AsyncCall (_, Some l, c, m, _, a) ->
	    print_string "call( ";
	    of_lhs l ;
	    print_string " ;";
	    print_space () ;
	    of_expression c ;
	    print_string " ;";
	    print_space () ;
	    print_string ("\"" ^ m ^ "\" ;") ;
	    print_space () ;
	    of_expression_list a;
	    print_string " )"
	| Statement.MultiCast (_, c, m, _, a) ->
	    print_string "multicast( ";
	    of_expression c ;
	    print_string (" ; \"" ^ m ^ "\" ; ") ;
	    of_expression_list a;
	    print_string " )"
	| Statement.Get (_, l, o) ->
	    print_string "get( " ;
	    of_expression l ;
	    print_string " ; " ;
	    of_lhs_list o;
	    print_string " )"
        | Statement.Free (_, [l]) ->
	    print_string "free( " ;
	    of_lhs l ;
            print_string " )"
        | Statement.Free (n, l::ls) ->
            print prec (Statement.Sequence (n, Statement.Free(n, [l]),
              Statement.Free(n, ls)))
        | Statement.Free (_, []) ->
	    assert false
	| Statement.Bury _ as s ->
	    print prec (Statement.assignment_of_bury s)
	| Statement.LocalSyncCall _ | Statement.AwaitLocalSyncCall _
	| Statement.LocalAsyncCall (_, None, _, _, _, _, _) ->
	    assert false
	| Statement.LocalAsyncCall (_, Some l, m, _, None, None, i) ->
	    (* An unqualified local synchronous call should use this in
	       order to get late binding correct. *)
	    print_string "call( " ;
	    of_lhs l ;
	    print_string (" ; \"this\" ; \"" ^ m ^ "\" ; ");
	    of_expression_list i ;
	    print_string " )"
	| Statement.LocalAsyncCall (_, Some l, m, _, Some lb, None, i) ->
	    print_string "static( " ;
	    of_lhs l ;
	    print_string
	      (" ; \"" ^ m ^ "\" ; \"" ^ lb ^ "\" ; None ; ");
	    of_expression_list i;
	    print_string " )"
	| Statement.LocalAsyncCall (_, Some _, _, _, _, _, _) ->
	    assert false
	| Statement.Tailcall (_, c, m, _, i) ->
	    print_string "tailcall (" ;
	    of_expression c ;
            print_string (" ; \"" ^ m ^ "\" ; ");
	    of_expression_list i;
	    print_string " )"
	| Statement.StaticTail (_, m, _, None, None, i) ->
	    print_string
		( "statictail (\"" ^ m ^ "\" ; None ; None ; ");
	    of_expression_list i;
	    print_string " )"
	| Statement.StaticTail (_, m, _, _, _, i) ->
	    assert false
	| Statement.Return (_, el) ->
	  print_string "return ( " ;
	  of_expression_list el ;
	  print_string " )"
	| Statement.If (_, c, t, f) ->
	    print_string "if"; print_space () ;
	    of_expression c ;
	    print_space () ; print_string "th"; print_space () ;
	    print 25 t ;
	    print_space () ; print_string "el" ; print_space () ;
	    print 25 f ;
	    print_space () ; print_string "fi"
	| Statement.While (_, c, _, b) ->
	    print_string "while" ; print_space () ;
	    of_expression c ;
	    print_space () ; print_string "do" ; print_space () ;
	    print 25 b ;
	    print_space () ; print_string "od "
	| Statement.DoWhile (n, c, i, b) ->
	    print 25 (Statement.Sequence (n, b, Statement.While (n, c, i, b)))
	| Statement.Sequence (_, s1, s2) ->
	    let op_prec = 25 in
	      open_paren prec op_prec ;
	      print op_prec s1 ; 
	      print_space () ; print_string ";" ; print_space () ;
	      print op_prec s2 ; 
	      close_paren prec op_prec
	| Statement.Merge (_, l, r) ->
	    let op_prec = 29 in
	      open_paren prec op_prec ;
	      print op_prec l ; 
	      print_space () ; print_string "|||" ; print_space () ;
	      print op_prec r ; 
	      close_paren prec op_prec
	| Statement.Choice (_, l, r) ->
	    let op_prec = 27 in
	      open_paren prec op_prec ;
	      print op_prec l ;
	      print_space () ; print_string "[]" ; print_space () ;
	      print op_prec r ; 
	      close_paren prec op_prec
        | Statement.Continue (_, label) ->
              print_string "$cont " ;
	      of_expression label
	| Statement.Extern _ ->
	    (* Should have been replaced by an assignment with
	       a (special) function call. *)
	    assert false
    in print 25 stmt
  and of_inherits  inh =
	print_string ("\"" ^ inh.Inherits.name ^ "\" < ");
	of_expression_list inh.Inherits.arguments ;
	print_string " >"
  and of_inherits_list =
    function
	[] -> print_string "noInh"
      | lst -> separated_list of_inherits print_comma lst
  and of_parameter { VarDecl.name = n } =
    print_string ("\"" ^ n ^ "\"")
  and of_parameter_list =
    function
	[] -> print_string "noVid"
      | lst -> separated_list of_parameter print_comma lst
  and of_vardecl { VarDecl.name = n } =
    print_string ("\"" ^ n ^ "\"") ;
    print_space () ;
    print_string "|->" ;
    print_space () ;
    print_string "null" 
  and of_class_attribute_list =
    function
	[] -> print_string "noSubst" 
      | lst -> separated_list of_vardecl print_comma lst
  and of_method cls m =
    let wildcard = { VarDecl.name = "_"; var_type = Type.data; init = None;
                     file = ""; line = 0; }
    in
      open_box 2 ;
      print_string ("< \"" ^ m.Method.name ^ "\" : Method | Param: ");
      of_parameter_list m.Method.inpars ;
      print_comma () ;
      print_string "Att: " ;
      of_class_attribute_list
        (List.concat [ m.Method.inpars ; m.Method.outpars ; m.Method.vars ;
		      [wildcard] ]) ;
      print_comma () ;
      print_string "Code: " ;
      begin
         match m.Method.body with
	   | None -> print_string "skip"
           | Some s -> of_statement s
      end ;
      print_space () ;
      print_string ">" ;
      close_box ()
  and of_method_list cls =
    function
	[] ->
          print_string "noMtd" 
      | lst ->
	  open_vbox 0 ;
          separated_list (of_method cls) print_comma lst ;
	  close_box ()
  and of_with_defs cls ws =
    let methods = List.flatten (List.map (function w -> w.With.methods) ws) in
      of_method_list cls methods
  and of_class c =
    open_box 2 ;
    print_string "< " ;
    begin
      match subtarget.target with
	| Updates -> print_string ("class(\"" ^ c.Class.name ^ "\", 0)")
	| _ -> print_string ("\"" ^ c.Class.name ^ "\"")
    end ;
    print_string " : Class |" ;
    begin
      match subtarget.target with
	| Updates -> print_space (); print_string ("Version: 0,")
	| _ -> ()
    end ;
    print_space () ;
    print_string "Inh: " ;
    of_inherits_list c.Class.inherits;
    print_comma () ;
    print_string "Param: ";
    of_parameter_list c.Class.parameters;
    print_comma () ;
    print_string "Att: " ;
    of_class_attribute_list (c.Class.parameters @ c.Class.attributes) ;
    print_comma () ;
    print_string "Mtds: " ;
    of_with_defs c.Class.name c.Class.with_defs ;
    print_comma () ;
    print_string ("Ocnt: " ^ (Big_int.string_of_big_int c.Class.objects_created) ^ " >") ;
    close_box ()
  and of_mapping =
    function
      | { VarDecl.name = name; init = Some init } ->
          print_string name ;
          print_space () ;
          print_string "|->" ;
          print_space () ;
          of_expression init ;
      | _ -> assert false
  and of_substitution =
    function
	[] -> print_string "noSubst"
      | lst -> separated_list of_mapping print_comma lst
  and of_process proc =
    print_string "{ " ;
    of_substitution proc.Process.attributes ;
    print_space () ;
    print_string "|" ;
    print_space () ;
    of_statement proc.Process.code ;
    print_string " }"
  and of_process_list =
    function
	[] -> print_string "noProc"
      | lst -> separated_list of_process print_comma lst
  and of_object obj =
    open_box 2 ;
    print_string "< " ;
    of_expression obj.Object.name ;
    print_string  " :" ;
    print_space () ;
    print_string ((Type.string_of_type obj.Object.cls) ^ " |") ;
    print_space () ;
    print_string "Att: " ;
    of_substitution obj.Object.attributes ;
    print_comma () ;
    print_string "Pr: ";
    of_process obj.Object.process ;
    print_comma () ;
    print_string "PrQ: " ;
    of_process_list obj.Object.process_queue ;
    print_comma () ;
    print_string ("Lcnt: " ^ (Big_int.string_of_big_int obj.Object.emitted_calls)) ;
    print_string " >";
    close_box ()
  and of_future f =
    open_box 2 ;
    print_string "< ";
    of_expression f.Future.name ;
    print_space () ;
    print_string ": Future |" ;
    print_space () ;
    print_string "Completed: " ;
    print_string (string_of_bool f.Future.completed) ;
    print_comma () ;
    print_string "References: ";
    print_string (Big_int.string_of_big_int f.Future.references) ;
    print_comma () ;
    print_string "Value: " ;
    of_expression_list f.Future.value ;
    print_string " >";
    close_box ()
  and of_declaration =
    function
	Declaration.Class c -> of_class c
      | Declaration.Interface _
      | Declaration.Exception _
      | Declaration.Datatype _
      | Declaration.Function _ -> assert false
      | Declaration.Future f -> of_future f
      | Declaration.Object o -> of_object o
  and of_decl_list =
    let relevant_p =
      function
	| Declaration.Class _ 
	| Declaration.Future _
	| Declaration.Object _ -> true
        | Declaration.Interface _
        | Declaration.Exception _
        | Declaration.Datatype _
        | Declaration.Function _ -> false
    in
    function
	{ Program.decls = [] } -> print_string "none\n"
      | { Program.decls = decls } ->
	  separated_list
	    of_declaration
	    (fun () -> print_space () ; print_space ())
	    (List.filter relevant_p decls)
  in
    (** Convert an abstract syntax tree l of a creol program to a
	representation for the Maude CMC and write the result to the
	output channel out. *)
    let () = set_formatter_out_channel out_channel in
      open_vbox 0 ;
      print_string ("load " ^ (interpreter subtarget.target) ^ " .") ;
      print_space () ;
      print_string "mod PROGRAM is" ;
      print_space () ;
      open_hbox () ; print_space () ; print_space () ; close_box () ;
      begin
        open_vbox 0 ;
        print_string "protecting CREOL-SIMULATOR ." ;
	print_space () ;
	print_string "op classes : -> Configuration [ctor] ." ;
	print_space () ;
	print_string "eq classes =" ;
	print_space () ;
        begin
          open_hbox () ; print_space () ; print_space () ; close_box () ;
	  open_vbox 0 ;
          of_decl_list input ;
	  print_string " ." ;
	  close_box ()
	end ;
	close_box ()
      end ;
      print_space () ;
      print_string "endm" ;
      print_space () ;
      if subtarget.target = Modelchecker then
        begin
	  print_space () ;
	  print_string "mod PROGRAM-CHECKER is" ;
	  print_space () ;
	  open_hbox () ; print_space () ; print_space () ; close_box () ;
	  open_vbox 0 ;
	  print_string "protecting MODEL-CHECKER ." ;
	  print_space () ;
	  print_string "protecting PROGRAM ." ;
	  print_space () ;
	  print_string "protecting CREOL-PREDICATES ." ;
	  close_box () ;
	  print_space () ;
	  print_string "endm"
        end ;
      close_box () ;
      print_newline ()
