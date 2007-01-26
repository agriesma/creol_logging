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
    | Await of guard
    | If of expression * statement * statement
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
