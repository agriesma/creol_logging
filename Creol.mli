
(** The abstract syntax of the (unspecified) Creol expression language or
    functional sub-language *)
type 'a expression =
    Nil of 'a
    | Int of 'a * int
    | Float of 'a * float
    | Bool of 'a * bool
    | Id of 'a * string
    | Unary of 'a * unaryop * 'a expression
    | Binary of 'a * binaryop * 'a expression * 'a expression
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

val statement_note: 'a statement -> 'a

val pretty_print: out_channel -> 'a declaration list -> unit

val simplify: 'a declaration list -> 'a declaration list

val maude_of_creol: out_channel -> 'a declaration list -> unit
