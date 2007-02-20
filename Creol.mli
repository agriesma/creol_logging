
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

type guard =
    Label of string
    | Condition of expression
    | Conjunction of guard * guard

type statement =
    Skip
    | Assign of string * expression
    | Await of guard
    | If of expression * statement * statement
    | New of string * string * expression list
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

val pretty_print: out_channel -> declaration list -> unit
