(*
 * Creol.ml -- Definition and manipulation of Creol AST
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

(** The abstract syntax of the (unspecified) Creol expression language or
    functional sub-language *)
type 'a expression =
    Nil of 'a
    | Int of 'a * int
    | Float of 'a * float
    | Bool of 'a * bool
    | String of 'a * string
    | Id of 'a * string
    | Unary of 'a * unaryop * 'a expression
    | Binary of 'a * binaryop * 'a expression * 'a expression
    | FuncCall of 'a * string * 'a expression list
and unaryop =
    Not
    | UMinus
and binaryop =
    Plus
    | Minus
    | Times
    | Div
    | Eq
    | Ne
    | Le
    | Lt
    | Ge
    | Gt
    | And
    | Or
    | Xor
    | Iff

type 'a guard =
    Wait of 'a
    | Label of 'a * string
    | Condition of 'a * 'a expression
    | Conjunction of 'a * 'a guard * 'a guard

type 'a statement =
    Skip of 'a
    | Assign of 'a * string * 'a expression
    | Await of 'a * 'a guard
    | If of 'a * 'a expression * 'a statement * 'a statement
    | New of 'a * string * string * 'a expression list
    | Sequence of 'a * 'a statement * 'a statement
    | Merge of 'a * 'a statement * 'a statement
    | Choice of 'a * 'a statement * 'a statement
    | ASyncCall of 'a * string option * 'a expression * string *
	'a expression list * string list option
    | SyncCall of 'a * 'a expression * string *
	'a expression list * string list

(** The abstract syntax of Creol *)
type 'a vardecl =
    { var_name: string; var_type: string; var_init: 'a expression option }

type 'a creolmethod =
    { meth_name: string;
      meth_coiface: string;
      meth_inpars: 'a vardecl list;
      meth_outpars: 'a vardecl list;
      meth_vars: 'a vardecl list;
      meth_body: 'a statement option }

type 'a inherits = string * ('a expression list)

type 'a classdecl =
    { cls_name: string;
      cls_parameters: 'a vardecl list;
      cls_inherits: 'a inherits list;
      cls_contracts: string list;
      cls_implements: string list;
      cls_attributes: 'a vardecl list;
      cls_methods: 'a creolmethod list }

type  'a interfacedecl =
    { iface_name: string;
      iface_inherits: string list;
      iface_methods: 'a creolmethod list }

type 'a declaration =
    Class of 'a classdecl
    | Interface of 'a interfacedecl

let statement_note =
  function
    Skip a -> a
    | Assign(a, _, _) -> a
    | Await(a, _) -> a
    | If(a, _, _, _) -> a
    | New(a, _, _, _) -> a
    | Sequence(a, _, _) -> a
    | Merge(a, _, _) -> a
    | Choice(a, _, _) -> a
    | ASyncCall(a, _, _, _, _, _) -> a
    | SyncCall(a, _, _, _, _) -> a


(** Normalise an abstract syntax tree by replacing all derived concepts
    with there basic equivalents *)
let rec simplify_expression =
  function
      Binary (a, Ge, l, r) -> Binary (a, Le, r, l)
    | Binary (a, Gt, l, r) -> Binary (a, Lt, r, l)
    | Binary (a, Ne, l, r) -> Unary(a, Not, Binary (a, Eq, l, r))
    | Binary (a, Xor, l, r) -> Unary(a, Not, Binary (a, Eq, l, r))
    | t -> t
and simplify_expression_list =
  function
      [] -> []
    | e::r -> (simplify_expression e)::(simplify_expression_list r)
and simplify_guard =
  function
      Condition (a, e) -> Condition (a, simplify_expression e)
    | Conjunction (a, g1, g2) -> Conjunction (a, simplify_guard g1,
					     simplify_guard g2)
    | l -> l
and simplify_statement =
  function
      Assign (a, s, e) -> Assign (a, s, simplify_expression e)
    | Await (a, g) -> Await (a, simplify_guard g)
    | If (a, c, t, f) -> If(a, simplify_expression c, simplify_statement t,
			   simplify_statement f)
    | New (a, s, c, p) -> New (a, s, c, simplify_expression_list p)
    | Sequence (a, s1, s2) -> Sequence (a, simplify_statement s1,
				       simplify_statement s2)
    | Merge (a, s1, s2) -> Merge (a, simplify_statement s1,
				 simplify_statement s2)
    | Choice (a, s1, s2) -> Choice (a, simplify_statement s1,
				   simplify_statement s2)
    | ASyncCall (a, l, e, n, p, r) ->
	ASyncCall (a, l, simplify_expression e, n,
		  simplify_expression_list p, r)
    | SyncCall (a, e, n, p, r) ->
	SyncCall (a, simplify_expression e, n, simplify_expression_list p, r)
    | s -> s
and simplify_parameter_list l =
  l
and simplify_method_variables note =
  function
      [] -> Skip note
    | [{ var_name = n; var_type = _; var_init = Some i }] ->
	Assign(note, n, simplify_expression i)
    | { var_name = n; var_type = _; var_init = Some i }::l ->
	Sequence(note, Assign(note, n, simplify_expression i),
		(simplify_method_variables note l))
    | _::l -> simplify_method_variables note l
and simplify_method m =
  { meth_name = m.meth_name;
    meth_coiface = m.meth_coiface;
    meth_inpars = m.meth_inpars;
    meth_outpars = m.meth_outpars;
    meth_vars = m.meth_vars;
    meth_body = match m.meth_body with
	None -> None
      | Some s ->
	  let note = statement_note s in
	    Some (Sequence(note, simplify_method_variables note m.meth_vars,
			 (simplify_statement s))) }
and simplify_method_list =
  function
      [] -> []
    | m::l -> (simplify_method m)::(simplify_method_list l)
and simplify_inherits =
  function
      (n, e) -> (n, simplify_expression_list e)
and simplify_inherits_list =
  function
      [] -> []
    | i::l -> (simplify_inherits i)::(simplify_inherits_list l)
and simplify_class c =
  { cls_name = c.cls_name;
    cls_parameters = simplify_parameter_list c.cls_parameters;
    cls_inherits = simplify_inherits_list c.cls_inherits;
    cls_contracts = c.cls_contracts;
    cls_implements = c.cls_implements;
    cls_attributes = c.cls_attributes;
    cls_methods = simplify_method_list c.cls_methods }
and simplify_interface i =
  i
and simplify =
  function
      [] -> []
    | Class c::l -> (Class (simplify_class c))::(simplify l)
    | Interface i::l -> (Interface (simplify_interface i))::(simplify l)

(* These are the support functions for the abstract syntax tree. *)

let rec pretty_print_expression out_channel =
  function
      Nil _ -> output_string out_channel "nil"
    | Int (_, i) -> output_string out_channel (string_of_int i)
    | Float (_, f) -> output_string out_channel (string_of_float f)
    | Bool (_, b) -> output_string out_channel (string_of_bool b)
    | Id (_, i) -> output_string out_channel i
    | Unary (_, o, e) ->
	output_string out_channel
	  (match o with Not ->  "(not " | UMinus -> "(- ");
	pretty_print_expression out_channel e;
	output_string out_channel ")"
    | Binary(_, o, l, r) ->
	output_string out_channel "(";
	pretty_print_expression out_channel l;
	output_string out_channel
	  (match o with
	      Plus -> " + "
	    | Minus -> " - "
	    | Times -> " * "
	    | Div -> " / "
	    | Le -> " <= "
	    | Lt -> " < "
	    | Ge -> " >= "
	    | Gt -> " > "
	    | Ne -> " /= "
	    | Eq -> " = "
	    | And -> " and "
	    | Iff -> " iff "
	    | Or -> " or "
	    | Xor -> " xor ");
	pretty_print_expression out_channel r;
	output_string out_channel ")"

let rec pretty_print_expression_list out_channel =
  function
      [] -> ()
    | e::[] -> pretty_print_expression out_channel e
    | e::l -> pretty_print_expression out_channel e;
	output_string out_channel ", ";
	pretty_print_expression_list out_channel l

let rec pretty_print_string_list out_channel =
  function
      [] -> ()
    | s::[] -> output_string out_channel s
    | s::r -> output_string out_channel (s ^ ", ");
	pretty_print_string_list out_channel r

let rec pretty_print_guard out_channel =
  function
      Wait _ -> output_string out_channel "wait"
    | Label(_, l) -> output_string out_channel (l ^ "?")
    | Condition (_, c) -> pretty_print_expression out_channel c
    | Conjunction (_, l, r) ->
	pretty_print_guard out_channel l;
	output_string out_channel " and ";
	pretty_print_guard out_channel r

let rec pretty_print_statement out_channel =
  function
      Skip _ -> output_string out_channel "skip";
    | If (_, c, t, f) ->
	output_string out_channel "if ";
	pretty_print_expression out_channel c;
	output_string out_channel " then ";
	pretty_print_statement out_channel t;
	output_string out_channel " else ";
	pretty_print_statement out_channel f;
	output_string out_channel " fi";
    | Await (_, g) -> 
	output_string out_channel "await ";
	pretty_print_guard out_channel g;
    | Sequence (_, l, r) -> 
	output_string out_channel "(";
	pretty_print_statement out_channel l;
	output_string out_channel "; ";
	pretty_print_statement out_channel r;
	output_string out_channel ")";
    | Merge (_, l, r) -> 
	output_string out_channel "(";
	pretty_print_statement out_channel l;
	output_string out_channel " ||| ";
	pretty_print_statement out_channel r;
	output_string out_channel ")";
    | Choice (_, l, r) -> 
	output_string out_channel "(";
	pretty_print_statement out_channel l;
	output_string out_channel " [] ";
	pretty_print_statement out_channel r;
	output_string out_channel ")"
    | New (_, i, c, a) ->
        output_string out_channel (i ^ " := new " ^ c);
	( match a with
	    [] -> ()
	  | _ -> output_string out_channel "(" ;
	      pretty_print_expression_list out_channel a ;
	      output_string out_channel ")" )
    | Assign (_, i, e) ->
	output_string out_channel i;
	output_string out_channel " := ";
	pretty_print_expression out_channel e
    | SyncCall (_, c, m, a, r) ->
	pretty_print_expression out_channel c ;
	output_string out_channel ("." ^ m);
	output_string out_channel "(" ;
	pretty_print_expression_list out_channel a;
	output_string out_channel "; " ;
	pretty_print_string_list out_channel r;
	output_string out_channel ")"
    | ASyncCall (_, l, c, m, a, r) ->
	(match l with
	    None -> ()
	  | Some l -> output_string out_channel l ) ;
	output_string out_channel "!";
	pretty_print_expression out_channel c ;
	output_string out_channel ("." ^ m);
	( match (a, r) with
	    ([], None) -> ()
	  | (_, None) -> output_string out_channel "(" ;
	      pretty_print_expression_list out_channel a;
	      output_string out_channel ")"
	  | (_, Some rl) -> output_string out_channel "(" ;
	      pretty_print_expression_list out_channel a;
	      output_string out_channel "; " ;
	      pretty_print_string_list out_channel rl;
	      output_string out_channel ")" )

let pretty_print_vardecl out_channel v =
  output_string out_channel (v.var_name ^ ": " ^ v.var_type );
  ( match v.var_init with
      Some e -> output_string out_channel " := " ;
	pretty_print_expression out_channel e
    | None -> () )

let rec pretty_print_vardecls out_channel p d s =
    function
	[] -> ()
      | v::[] -> output_string out_channel p;
	  pretty_print_vardecl out_channel v;
	  output_string out_channel s
      | v::r -> output_string out_channel p;
	  pretty_print_vardecl out_channel v;
	  output_string out_channel d;
	  pretty_print_vardecls out_channel p d s r

let rec pretty_print_methods out_channel =
    function
	[] -> ()
      | m::r -> output_string out_channel
	  ("with " ^ m.meth_coiface ^ "op " ^ m.meth_name ^ "(") ;
	  (match m.meth_inpars with
	      [] -> ()
	    | l -> output_string out_channel "in ";
		pretty_print_vardecls out_channel "" ", " "" l) ;
	  (match m.meth_outpars with
	      [] -> ()
	    | l -> output_string out_channel "; out ";
		pretty_print_vardecls out_channel "" ", " "" l );
	  output_string out_channel ")" ;
	  pretty_print_vardecls out_channel "var " ";" ";" m.meth_vars;
	  (match m.meth_body with
	      None -> ()
	    | Some s -> output_string out_channel " == " ;
		pretty_print_statement out_channel s);
	  output_string out_channel "\n";
	  pretty_print_methods out_channel r

let pretty_print_class out_channel c =
  output_string out_channel ("class " ^ c.cls_name ^ " ") ;
  ( match c.cls_parameters with
	[] -> ()
      | l -> output_string out_channel "(";
	  pretty_print_vardecls out_channel "" ", " "" l;
	  output_string out_channel ")" ) ;
  ( match c.cls_inherits with
	[] -> ()
      | l -> output_string out_channel "\ninherits " ) ;
  ( match c.cls_contracts with
	[] -> ()
      | l -> output_string out_channel "\ncontracts " );
  ( match c.cls_implements with
	[] -> ()
      | l -> output_string out_channel "\nimplements " ) ;
  output_string out_channel "\nbegin\n";
  pretty_print_vardecls out_channel "var " "\n" "\n" c.cls_attributes ;
  pretty_print_methods out_channel c.cls_methods ;
  output_string out_channel "end\n\n"

let pretty_print_iface out_channel i =
  output_string out_channel "interface ";
  output_string out_channel i.iface_name;
  output_string out_channel "\nbegin\n";  
  output_string out_channel "end\n\n"

let rec pretty_print out_channel =
  function
      [] -> flush out_channel
    | Class c::l -> pretty_print_class out_channel c;
	pretty_print out_channel l
    | Interface i::l -> pretty_print_iface out_channel i;
	pretty_print out_channel l





(* Write a Creol program as a maude term. If the program is parsable
   but not semantically correct, this function will only produce
   garbage. *)

let rec maude_of_creol_expression out =
  function
      Nil _ -> output_string out "null"
    | Int (_, i) -> output_string out ("int(" ^ (string_of_int i) ^ ")")
    | Float (_, f) -> ()
    | Bool (_, false) -> output_string out "bool(false)"
    | Bool (_, true) -> output_string out "bool(true)"
    | String (_, s) -> output_string out ("\"" ^ s ^ "\"")
    | Id (_, i) -> output_string out ("'" ^ i)
    | Unary (_, o, e) ->
	output_string out ( "( " ^ (match o with
	    Not ->  "'not"
	  | UMinus -> "'neg") ^ " [[ ");
	maude_of_creol_expression out e;
	output_string out "]] )"
    | Binary (_, o, l, r) ->
	output_string out ("( " ^ (match o with
	    Plus -> "'plus"
	  | Minus -> "'minus"
	  | Times -> "'times"
	  | Div -> "'div"
          | And -> "'and"
          | Iff -> "'equal"
          | Or -> "'or"
          | Lt -> "'less"
          | Le -> "'lessEq"
          | Eq -> "'equal"
	  | (Xor|Gt|Ge|Ne) -> assert false) ^ "[[");
	maude_of_creol_expression_list out (l::[r]);
	output_string out "]] )"
and maude_of_creol_expression_list out_channel =
  function
      [] -> output_string out_channel "emp"
    | [e] -> maude_of_creol_expression out_channel e
    | e::l -> maude_of_creol_expression out_channel e;
	output_string out_channel " # ";
	maude_of_creol_expression_list out_channel l
and maude_of_creol_identifier_list out_channel =
  function
      [] -> output_string out_channel "emp"
    | [i] -> output_string out_channel ("'" ^ i)
    | i::l -> output_string out_channel ("'" ^ i ^ " # ");
	maude_of_creol_identifier_list out_channel l

let rec maude_of_creol_string_list out_channel =
  function
      [] -> ()
    | s::[] -> output_string out_channel ("'" ^ s)
    | s::l -> output_string out_channel ("'" ^ s ^ ", ");
	maude_of_creol_string_list out_channel l

let rec maude_of_creol_guard out =
  function
      Label (_, l) -> output_string out ("( '" ^ l ^ " ? )")
    | Wait _ -> output_string out "wait"
    | Condition (_, c) -> maude_of_creol_expression out c
    | Conjunction (_, l, r) ->
	output_string out "( "; maude_of_creol_guard out l;
	output_string out " 'and "; maude_of_creol_guard out r ;
	output_string out ") "

let rec maude_of_creol_statement out =
  function
      Skip _ -> output_string out "skip"
    | Await (_, g) -> output_string out "await "; maude_of_creol_guard out g
    | If (_, c, t, Skip _) ->
	output_string out "if ("; maude_of_creol_expression out c;
	output_string out ") th ("; maude_of_creol_statement out t;
	output_string out ") fi"
    | If (_, c, t, f) ->
	output_string out "if ("; maude_of_creol_expression out c;
	output_string out ") th ("; maude_of_creol_statement out t;
	output_string out ") el ("; maude_of_creol_statement out f;
	output_string out ") fi"
    | Sequence (_, l, r) ->
	output_string out "( ("; maude_of_creol_statement out l; 
	output_string out ") ; ("; maude_of_creol_statement out r; 
	output_string out ") )"
    | Merge (_, l, r) ->
	output_string out "( "; maude_of_creol_statement out l; 
	output_string out " ||| "; maude_of_creol_statement out r; 
	output_string out " )"
    | Choice (_, l, r) ->
	output_string out "( "; maude_of_creol_statement out l; 
	output_string out " [] "; maude_of_creol_statement out r; 
	output_string out " )"
    | New (_, i, c, a) ->
	output_string out ("'" ^ i ^ " ::= new '" ^ c ^ "(") ;
	maude_of_creol_expression_list out a ;
	output_string out ")"
    | Assign (_, i, e) ->
	output_string out ("'" ^ i ^ " ::= ") ;
	maude_of_creol_expression out e
    | ASyncCall (_, l, c, m, a, r) ->
	(match l with
	    None -> ()
	  | Some l -> output_string out ("'" ^ l) ) ;
	output_string out " ! ";
	maude_of_creol_expression out c ;
	output_string out (" . '" ^ m ^ " ( ") ;
	maude_of_creol_expression_list out a;
	( match r with
	    None -> ()
	  | Some rl ->
	      output_string out " ; " ;
	      maude_of_creol_identifier_list out rl ) ;
	output_string out ")"
    | SyncCall (_, c, m, a, r) ->
	maude_of_creol_expression out c ;
	output_string out (" . '" ^ m);
	output_string out "(" ;
	maude_of_creol_expression_list out a;
	output_string out " ; " ;
	maude_of_creol_identifier_list out r;
	output_string out ")"


let maude_of_creol_attribute out a =
  output_string out ("(" ^ a.var_name ^ ": ");
  (match a.var_init with
      None -> output_string out "null"
    | Some e -> maude_of_creol_expression out e);
  output_string out ")"

let rec maude_of_creol_attribute_list out =
  function
      [] ->  output_string out "none"
    | [a] -> maude_of_creol_attribute out a
    | a::l -> maude_of_creol_attribute out a; output_string out ", ";
	maude_of_creol_attribute_list out l

let maude_of_creol_inherits out =
  function
      (i, l) -> output_string out (i ^ "<");
	maude_of_creol_expression_list out l;
	output_string out ">"

let rec maude_of_creol_inherits_list out =
  function
      [] -> output_string out "noInh"
    | [i] -> maude_of_creol_inherits out i
    | i::r -> maude_of_creol_inherits out i;
	output_string out " ## ";
	maude_of_creol_inherits_list out r

let rec maude_of_creol_parameter_list out =
  function
      [] -> output_string out "noAid"
    | [v] -> output_string out ("'" ^ v.var_name)
    | v::r ->output_string out ("'" ^ v.var_name ^ " ,, ");
	maude_of_creol_parameter_list out r

let rec maude_of_creol_class_attribute_list out =
  function
      [] -> output_string out "empty" 
    | [v] -> output_string out ("'" ^ v.var_name ^ " |-> null")
    | v::r -> output_string out ("'" ^ v.var_name ^ " |-> null , ");
	maude_of_creol_class_attribute_list out r

let rec maude_of_creol_method_return out =
  function
      [] -> output_string out "emp" 
    | [n] -> output_string out ("'" ^ n.var_name)
    | n::l -> output_string out ("'" ^ n.var_name ^ " # ");
        maude_of_creol_method_return out l

let maude_of_creol_method out m =
  output_string out ("\n  < '" ^ m.meth_name ^ " : Mtdname | Param: ");
  maude_of_creol_parameter_list out m.meth_inpars;
  output_string out ", Latt: " ;
  maude_of_creol_class_attribute_list out
    (m.meth_inpars @ m.meth_outpars @ m.meth_vars);
  output_string out ", Code: " ;
  ( match m.meth_body with
      None -> output_string out "skip"
    | Some s -> maude_of_creol_statement out s ;
	output_string out " ; return ( ";
	maude_of_creol_method_return out m.meth_outpars;
	output_string out " )" ) ;
  output_string out " >"

let rec maude_of_creol_method_list out =
  function
      [] -> output_string out "empty" 
    | [m] -> maude_of_creol_method out m
    | m::r -> maude_of_creol_method out m;
	output_string out " *";
	maude_of_creol_method_list out r

let maude_of_creol_class out c =
  output_string out ("< \'" ^ c.cls_name ^ " : Cl | Inh: ");
  maude_of_creol_inherits_list out c.cls_inherits;
  output_string out ", Par: ";
  maude_of_creol_parameter_list out c.cls_parameters;
  output_string out ", Att: ";
  maude_of_creol_class_attribute_list out
    (c.cls_parameters @ c.cls_attributes);
  output_string out ", Mtds: ";
  maude_of_creol_method_list out c.cls_methods;
  output_string out ", Ocnt: 0 >\n\n"

let maude_of_creol_interface out i = ()

let rec maude_of_creol_decl_list out =
  function
      [] -> ()
    | Class c::l -> maude_of_creol_class out c;
	maude_of_creol_decl_list out l
    | Interface i::l -> maude_of_creol_interface out i;
	maude_of_creol_decl_list out l

(** Convert an abstract syntax tree l of a creol program to a
    representation for the Maude CMC and write the result to the output
    channel out. *)
let maude_of_creol out l =
  output_string out "load interpreter\nmod PROGRAM is\npr INTERPRETER .\nop init : -> Configuration [ctor] .\neq init =\n" ;
  maude_of_creol_decl_list out l ;
  output_string out ".\nendm\n" ;
  flush out
