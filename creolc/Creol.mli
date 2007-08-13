(*
 * Creol.mli -- Definition and manipulation of Creol AST
 *
 * This file is part of creoltools
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

module Type :
  sig

    type note

    val make_note : Lexing.position -> note

    val label : string

    type t = 
	Basic of note * string
	| Variable of note * string
	| Application of note * string * t list
	| Tuple of note * t list
	| Function of note * t list * t
	| Structure of note * field list
	| Variant of note * field list
	| Intersection of note * t list
	| Union of note * t list
    and field =
	{ field_note: note;
	  field_name: string;
	  field_type: t   
	}

    val line : t -> int

    val file : t -> string

    val as_string : t -> string
  end

module Expression :
sig
  type note

  val make_note : Lexing.position -> note

  type  t =
	This of note
	(** The name of this. *)
      | Caller of note
	(** The name of the caller in a method. *)
      | Now of note
	(** The current time *)
      | Null of note
	(** Literal of the null pointer. *)
      | Nil of note
	  (** Literal for an empty list. *)
      | Bool of note * bool
	  (** A boolean literal. *)
      | Int of note * int
	  (** An integer literal. *)
      | Float of note * float
	  (** A floating point literal. *)
      | String of note * string
	  (** A string literal. *)
      | Id of note * string
	  (** An identifier, usually an attribute or a local variable name *)
      | StaticAttr of note * string * Type.t
	  (** Class-qualified access to an attribute value. *)
      | Tuple of note * t list
	  (** Tuple expression. *)
      | ListLit of note * t list
	  (** A list literal expression, enumerating its elements. *)
      | SetLit of note * t list
	  (** A set literal expression, enumerating its elements. *)
      | FieldAccess of note * t * string
	  (** Access the field of a structure. *)
      | Unary of note * unaryop * t
	  (** A unary expression *)
      | Binary of note * binaryop * t * t
	  (** A binary expression *)
      | If of note * t * t * t
	  (** Conditional expression *)
      | FuncCall of note * string * t list
	  (** A call of a primitive function *)
      | Label of note * t
	  (** The label expression, permitted only in guards.  The
              sub-expression {i must} be an [Id] or [SSAId]. *)
      | New of note * Type.t * t list
	  (** Object creation expression, permitted only as top nodes *)
      | Extern of note * string
	  (** The body of a function which is defined externally, for
	      example, in Maude or C *)
      | SSAId of note * string * int
	  (** An identifier in SSA form, usually local variable name *)
      | Phi of note * t list
	  (** A Phi expression used in SSA format *)
  and lhs =
      (** These forms may occur on the left hand side of assignments *)
      LhsVar of note * string
	  (** An assignable variable. *)
    | LhsAttr of note * string * Type.t
	  (** An assignable statically qualified class member. *)
    | LhsWildcard of note * Type.t option
	  (** An expression which can accept any value. *)
    | LhsSSAId of note * string * int
	  (** An identifier in SSA form, usually local variable name *)
  and unaryop =
      (** Definition of the different unary operator symbols *)
      Not
	(** The negation of boolean values *)
      | UMinus
	  (** Invert a floating point number or an integer. *)
      | Length
	  (** The length of an expression *)
  and binaryop =
      (** Definition of the different binary operator symbols *)
      Plus
      | Minus
      | Times
      | Div
      | Modulo
      | Power
      | Eq
      | Ne
      | Le
      | Lt
      | Ge
      | Gt
      | And
      | Or
      | Xor
      | Implies
      | Iff
      | Prepend
      | Append
      | Concat
      | Project
      | In

  val string_of_binaryop : binaryop -> string

  val prec_of_binaryop : binaryop -> (int * int)

  val string_of_unaryop : unaryop -> string

  val prec_of_unaryop : unaryop -> int

  val note : t -> note
end

module Statement: sig

  type note

  val make_note : Lexing.position -> note
      (** Create a new note *)

  type t =
      (** Abstract syntax of statements in Creol.  The type parameter ['a]
	  refers to the type of possible annotations. *)
      Skip of note
	(** A skip statement *)
      | Release of note
	(** A release statement *)
      | Assert of note * Expression.t
	(** Check a condition at runtime. *)
      | Assign of note * Expression.lhs list * Expression.t list
	  (** A multiple assignment statement.  Requires that the two lists
	      are of the same length. *)
      | Await of note * Expression.t
	  (** An await statement. *)
      | Posit of note * Expression.t
	  (** A posit statement, which is used to define {i true} properties
              about time in a model. *)
      | AsyncCall of note * Expression.lhs option * Expression.t * string *
	  Expression.t list
	  (** Call a method asynchronously. *)
      | Reply of note * Expression.t * Expression.lhs list
	  (** Receive the reply to an asynchronous call. *)
      | Free of note * Expression.t list
	  (** Release labels.  The labels are not usable after
	      executing this statement anymore. The argument {i must}
	      refer to a list of Id or SSAId. *)
      | SyncCall of note * Expression.t * string *
	  Expression.t list * Expression.lhs list
	  (** Call a (remote) method synchronously. *)
      | AwaitSyncCall of note * Expression.t * string *
	  Expression.t list * Expression.lhs list
	  (** Call a (remote) method synchronously. *)
      | LocalAsyncCall of note * Expression.lhs option * string *
	  string option * string option * Expression.t list
	  (** Call a local method synchronously. *)
      | LocalSyncCall of note * string * string option * string option *
	  Expression.t list * Expression.lhs list
	  (** Call a local method synchronously. *)
      | AwaitLocalSyncCall of note * string * string option * string option *
	  Expression.t list * Expression.lhs list
	  (** Call a local method synchronously. *)
      | Tailcall of note * string * string option * string option *
	  Expression.t list
	  (** Internal statement for eliminating tail calls. *)
      | If of note * Expression.t * t * t
	  (** Conditional execution. *)
      | While of note * Expression.t * Expression.t option * t
	  (** While loops. *)
      | Sequence of note * t * t
	  (** Sequential composition *)
      | Merge of note * t * t
	  (** Merge of statements *)
      | Choice of note * t * t
	  (** Choice between statements *)
      | Extern of note * string
	  (** The method body or function body is defined externally.
	      This statement is not allowed to be composed. **)

  val note: t -> note

  val is_skip_p: t -> bool

  val normalize_sequences: t -> t

  val simplify_assignment: t -> t

  val remove_redundant_skips: t -> t
end



module VarDecl :
  sig
    type t =
    (** Abstract syntax representing a variable declaration. *)
    { name: string;
	(** Name of the variable. *)
      var_type: Type.t;
	(** Type of the variable. *)
      init: Expression.t option
	(** Expression used for initialisation. *)
    }
  end

module Method :
  sig

    type t =
    (** Abstract syntax of a method declaration and definition. *)
      { meth_name: string;
	  (** The name of the method. *)
        meth_inpars: VarDecl.t list;
	  (** A list of input parameters. *)
        meth_outpars: VarDecl.t list;
	  (** A list of output parameters. *)
        meth_vars: VarDecl.t list;
	  (** A list of local variables. *)
        meth_body: Statement.t option
	  (** The method body. *)
      }

  end





(** Abstract syntax of a with clause.

    A with clause consists of a co-interface name, a list of methods
    and a sequence of invariants. *)
module With: sig

  type t = {
    co_interface: string option;
    methods: Method.t list;
    invariants: Expression.t list
  }

end






module Class : sig

  type inherits = string * Expression.t list

  type t =
      { name: string;
	parameters: VarDecl.t list;
	inherits: inherits list;
	contracts: inherits list;
	implements: inherits list;
	attributes: VarDecl.t list;
	with_defs: With.t list }

end





module Interface : sig

  type inherits = string * Expression.t list

  type t =
    { name: string;
      inherits: inherits list;
      with_decl: With.t list }

end





module Operation : sig

  type t = {
    name: string;
    parameters: VarDecl.t list;
    result_type: Type.t;
    body: Expression.t
  }

end

(** Signature of a data type declaration. *)
module Datatype :
  sig

    type t = {
      name: Type.t;
      supers: Type.t list;
      operations: Operation.t list
    }

  end





module Exception :
  sig

    type t = { name: string; parameters: VarDecl.t list }

  end




module Declaration : sig

  type t =
      Class of Class.t
      | Interface of Interface.t
      | Datatype of Datatype.t
      | Exception of Exception.t

end

module Program :
  sig

    type t = Declaration.t list

  end

val make_expr_note_from_stmt_note : Statement.note -> Expression.note
