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
type expression =
    Int of int
    | Float of float
    | Bool of bool
    | Id of string
    | Unary of unaryop * expression
    | Binary of binaryop * expression * expression
and unaryop =
    Not
    | UMinus
and binaryop =
    Plus
    | Minus
    | Times
    | Div

type guard =
    Label of string
    | Condition of expression
    | Conjunction of guard * guard

type statement =
    Skip
    | Assign of string * expression
    | Await of guard
    | If of expression * statement * statement
    | New of string * expression list
    | Sequence of statement * statement
    | Merge of statement * statement
    | Choice of statement * statement

(** The abstract syntax of Creol *)
type vardecl =
    { var_name: string; var_type: string; var_init: expression option }

type creolmethod =
    { meth_name: string;
      meth_coiface: string;
      meth_inpars: vardecl list;
      meth_outpars: vardecl list;
      meth_body: statement option }

type inherits = string * (expression list)

type classdecl =
    { cls_name: string;
      cls_parameters: vardecl list;
      cls_inherits: inherits list;
      cls_contracts: string list;
      cls_implements: string list;
      cls_attributes: vardecl list;
      cls_methods: creolmethod list }

type  interfacedecl =
    { iface_name: string;
      iface_inherits: string list;
      iface_methods: creolmethod list }

type declaration =
    Class of classdecl
    | Interface of interfacedecl

(* These are the support functions for the abstract syntax tree. *)

let rec pretty_print_expression out_channel =
  function
      Int i -> output_string out_channel (string_of_int i)
    | Float f -> output_string out_channel (string_of_float f)
    | Bool b -> output_string out_channel (string_of_bool b)
    | Id i -> output_string out_channel i
    | Unary (o, e) ->
	output_string out_channel (match o with Not ->  "(not " | UMinus -> "(- ");
	pretty_print_expression out_channel e;
	output_string out_channel ")"
    | Binary(o, l, r) ->
	output_string out_channel "(";
	pretty_print_expression out_channel l;
	output_string out_channel
	  (match o with
	      Plus -> " + "
	    | Minus -> " - "
	    | Times -> " * "
	    | Div -> " / ");
	pretty_print_expression out_channel r;
	output_string out_channel ")"

let rec pretty_print_guard out_channel =
  function
      Label l -> output_string out_channel l; output_string out_channel "?"
    | Condition c -> pretty_print_expression out_channel c
    | Conjunction (l, r) ->
	pretty_print_guard out_channel l;
	output_string out_channel " and ";
	pretty_print_guard out_channel r

let rec pretty_print_statement out_channel =
  function
      Skip -> output_string out_channel "skip";
    | If (c, t, f) ->
	output_string out_channel "if ";
	pretty_print_expression out_channel c;
	output_string out_channel "then ";
	pretty_print_statement out_channel t;
	output_string out_channel "else ";
	pretty_print_statement out_channel f;
	output_string out_channel "fi ";
    | Await g -> 
	output_string out_channel "await ";
	pretty_print_guard out_channel g;
    | Sequence (l, r) -> 
	output_string out_channel "(";
	pretty_print_statement out_channel l;
	output_string out_channel "; ";
	pretty_print_statement out_channel r;
	output_string out_channel ")";
    | Merge (l, r) -> 
	output_string out_channel "(";
	pretty_print_statement out_channel l;
	output_string out_channel " ||| ";
	pretty_print_statement out_channel r;
	output_string out_channel ")";
    | Choice (l, r) -> 
	output_string out_channel "(";
	pretty_print_statement out_channel l;
	output_string out_channel " [] ";
	pretty_print_statement out_channel r;
	output_string out_channel ")"

let pretty_print_class out_channel c =
  output_string out_channel "class ";
  output_string out_channel c.cls_name;
  output_string out_channel "begin ";  
  output_string out_channel " end"

let pretty_print_iface out_channel i =
  output_string out_channel "interface ";
  output_string out_channel i.iface_name;
  output_string out_channel "begin ";  
  output_string out_channel " end"

let rec pretty_print out_channel =
  function
      [] -> flush out_channel
    | Class c::l -> pretty_print_class out_channel c; pretty_print out_channel l
    | Interface i::l -> pretty_print_iface out_channel i; pretty_print out_channel l


(* Write a Creol program as a maude term. If the program is parsable
   but not semantically correct, this function will only produce
   garbage. *)

let rec maude_of_creol_expression out =
  function
      Int i -> output_string out ("int(" ^ (string_of_int i) ^ ")")
    | Float f -> ()
    | Bool false -> output_string out "bool(false)"
    | Bool true -> output_string out "bool(true)"
    | Id i -> output_string out ("'" ^ i)
    | Unary (o, e) ->
	output_string out "(";
	output_string out (match o with Not ->  "not" | UMinus -> "-");
	maude_of_creol_expression out e;
	output_string out ")"
    | Binary (o, l, r) ->
	output_string out "("; maude_of_creol_expression out l;
	output_string out (match o with
	    Plus -> " + "
	  | Minus -> " - "
	  | Times -> " * "
	  | Div -> " / "); 
	maude_of_creol_expression out r; output_string out ")"

let rec maude_of_creol_guard out =
  function
      Label l -> ()
    | Condition c -> maude_of_creol_expression out c
    | Conjunction (l, r) -> maude_of_creol_guard out l;
	output_string out " 'and "; maude_of_creol_guard out r

let rec maude_of_creol_statement out =
  function
      Skip -> ()
    | Await g -> output_string out "await "; maude_of_creol_guard out g
    | If (c, t, Skip) ->
	output_string out "if "; maude_of_creol_expression out c;
	output_string out " th "; maude_of_creol_statement out t;
	output_string out " fi"
    | If (c, t, f) ->
	output_string out "if "; maude_of_creol_expression out c;
	output_string out " th "; maude_of_creol_statement out t;
	output_string out " el "; maude_of_creol_statement out f;
	output_string out " fi"
    | Sequence (l, r) ->
	output_string out "( "; maude_of_creol_statement out l; 
	output_string out " ; "; maude_of_creol_statement out r; 
	output_string out " )"
    | Merge (l, r) ->
	output_string out "( "; maude_of_creol_statement out l; 
	output_string out " ||| "; maude_of_creol_statement out r; 
	output_string out " )"
    | Choice (l, r) ->
	output_string out "( "; maude_of_creol_statement out l; 
	output_string out " [] "; maude_of_creol_statement out r; 
	output_string out " )"

let maude_of_creol_attribute out a =
  output_string out ("(" ^ a.var_name ^ ": ");
  (match a.var_init with
      None -> output_string out "null"
    | Some e -> maude_of_creol_expression out e);
  output_string out ")"

let rec maude_of_creol_attributes out =
  function
      [] ->  output_string out "none"
    | [a] -> maude_of_creol_attribute out a
    | a::l -> maude_of_creol_attribute out a; output_string out ", ";
	maude_of_creol_attributes out l

let maude_of_creol_class out c =
  output_string out ("< \'" ^ c.cls_name ^ " : Cl | Att: ");
  output_string out ">"

let maude_of_creol_interface out i = ()

let rec maude_of_creol out =
  function
      [] -> flush out
    | Class c::l -> maude_of_creol_class out c; maude_of_creol out l
    | Interface i::l -> maude_of_creol out l (* they dont exist in Maude *)
