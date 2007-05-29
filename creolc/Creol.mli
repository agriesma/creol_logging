(*
 * Creol.mli -- Definition and manipulation of Creol AST
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

(** Definition of the abstract syntax of Creol and a collection
    of functions for its manipulation.

    @author Marcel Kyas
    @version 0.0
    @since   0.0

 *)

(** Note of a statement and expession, as generated by the Parser.

    This signature is the minimum needed by compiler. *)
module Note :
  sig
    type t
    val make : Lexing.position -> t
      (** Create a new note *)
    val line : t -> int
      (** Get the line of a note *)
    val file : t -> string
      (** Get the file of a note *)
    val to_xml : XmlTextWriter.xmlwriter -> t -> unit
      (** Write a note to an XML file. *)
  end

(** Types *)
module Type :
  sig
    type t = 
	(** A type as defined in Creol. *)
	Basic of string
	  (** A basic type. *)
	| Application of string * t list
	    (** A type application. *)
	| Variable of string
	    (** A type variable. *)
	| Label

    val as_string : t -> string
  end

module Pattern :
sig
  type ('a, 'b, 'c) t =
    { pattern: 'a; when_clause: 'b option; match_clause: 'c }
end
 

module Case :
sig

  type ('a, 'b, 'c, 'd) t =
    { what: 'a; cases: ('b, 'c, 'd) Pattern.t list }
end

module Try :
sig
  type ('a, 'b, 'c, 'd) t =
    { what: 'a; catches: ('b, 'c, 'd) Pattern.t list }
end



module Expression :
sig
  type 'a t =
      (** Definition of the abstract syntax of Creol-expressions.
	  
          The parameter 'a refers to a possible annotation of the
          element. *)
      Null of 'a
	(** Literal of the null pointer. *)
      | Nil of 'a
	  (** Literal for an empty list. *)
      | Bool of 'a * bool
	  (** A boolean literal. *)
      | Int of 'a * int
	  (** An integer literal. *)
      | Float of 'a * float
	  (** A floating point literal. *)
      | String of 'a * string
	  (** A string literal. *)
      | Id of 'a * string
	  (** An identifier, usually an attribute or a local variable name *)
      | Tuple of 'a * 'a t list
	  (** Tuple expression. *)
      | Cast of 'a * 'a t * Type.t
	  (** Re-type an expression.  Involves a run-time check *)
      | Index of 'a * 'a t * 'a t
	  (** Convenience for indexing a sequence/vector/array *)
      | FieldAccess of 'a * 'a t * string
	  (** Access the field of a structure. *)
      | Unary of 'a * unaryop * 'a t
	  (** A unary expression *)
      | Binary of 'a * binaryop * 'a t * 'a t
	  (** A binary expression *)
      | If of 'a * 'a t * 'a t * 'a t
	  (** Conditional expression *)
      | Case of 'a * ('a t, unit, 'a t, 'a t) Case.t
	  (** Case expression *)
      | Typecase of 'a * ('a t, Type.t, 'a t, 'a t) Case.t
	  (** Type case expression *)
      | FuncCall of 'a * string * 'a t list
	  (** A call of a primitive function *)
      | Label of 'a * string
	  (** The label expression, permitted only in guards *)
      | New of 'a * Type.t * 'a t list
	  (** Object creation expression, permitted only as top nodes *)
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
      | Exponent
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
      | LAppend
      | RAppend
      | Concat
      | Project
      | In
      | GuardAnd

  val string_of_binaryop : binaryop -> string

  val string_of_unaryop : unaryop -> string

  val note : 'a t -> 'a
end

module Statement: sig
  type ('a, 'b) t =
      (** Abstract syntax of statements in Creol.  The type parameter ['a]
	  refers to the type of possible annotations. *)
      Skip of 'a
	(** A skip statement *)
      | Release of 'a
	(** A release statement *)
      | Assert of 'a * 'b Expression.t
	(** Check a condition at runtime. *)
      | Assign of 'a * string list * 'b Expression.t list
	  (** A multiple assignment statement.  Requires that the two lists
	      are of the same length. *)
      | Await of 'a * 'b Expression.t
	  (** An await statement. *)
      | AsyncCall of 'a * string option * 'b Expression.t * string *
	  'b Expression.t list
	  (** Call a method asynchronously. *)
      | Reply of 'a * string * string list
	  (** Receive the reply to an asynchronous call. *)
      | Free of 'a * string
	  (** Release a label.  It is not usable after executing this statement
	      anymore. *)
      | SyncCall of 'a * 'b Expression.t * string *
	  'b Expression.t list * string list
	  (** Call a (remote) method synchronously. *)
      | AwaitSyncCall of 'a * 'b Expression.t * string *
	  'b Expression.t list * string list
	  (** Call a (remote) method synchronously. *)
      | LocalAsyncCall of 'a * string option * string * string option *
	  string option * 'b Expression.t list
	  (** Call a local method synchronously. *)
      | LocalSyncCall of 'a * string * string option * string option *
	  'b Expression.t list * string list
	  (** Call a local method synchronously. *)
      | AwaitLocalSyncCall of 'a * string * string option * string option *
	  'b Expression.t list * string list
	  (** Call a local method synchronously. *)
      | Tailcall of 'a * string * string option * string option *
	  'b Expression.t list
	  (** Internal statement for eliminating tail calls. *)
      | If of 'a * 'b Expression.t * ('a, 'b) t * ('a, 'b) t
	  (** Conditional execution. *)
      | While of 'a * 'b Expression.t * 'b Expression.t option * ('a, 'b) t
	  (** While loops. *)
      | For of 'a * string * 'b Expression.t * 'b Expression.t *
	  'b Expression.t option * 'b Expression.t option * ('a, 'b) t
	  (** For loop *)
      | Raise of 'a * string * 'b Expression.t list
	  (** Raising an exception *)
      | Try of 'a * ('a, 'b) t * ('a, 'b) catcher list
	  (** Try and catch exception *)
      | Case of 'a * ('b Expression.t, unit, 'b Expression.t, ('a, 'b) t) Case.t
	  (** Case statement *)
      | Typecase of 'a * ('b Expression.t, Type.t, 'b Expression.t, ('a, 'b) t) Case.t
	  (** Type case statement *)
      | Sequence of 'a * ('a, 'b) t list
	  (** Sequential composition *)
      | Merge of 'a * ('a, 'b) t * ('a, 'b) t
	  (** Merge of statements *)
      | Choice of 'a * ('a, 'b) t * ('a, 'b) t
	  (** Choice between statements *)
  and  ('a, 'b) catcher =
      { catch: string option;
	catch_parameters: string list;
	catch_statement: ('a, 'b) t }
  and ('a, 'b) typecase =
      { with_type: Type.t option; with_statement: ('a, 'b) t }


  val note: ('a, 'b) t -> 'a
end



type 'a creol_vardecl =
    (** Abstract syntax representing a variable declaration. *)
    { var_name: string;
	(** Name of the variable. *)
      var_type: Type.t;
	(** Type of the variable. *)
      var_init: 'a Expression.t option
	(** Expression used for initialisation. *)
    }

type ('a, 'b) creolmethod =
    (** Abstract syntax of a method declaration and definition. *)
    { meth_name: string;
	(** The name of the method. *)
      meth_inpars: 'b creol_vardecl list;
	(** A list of input parameters. *)
      meth_outpars: 'b creol_vardecl list;
	(** A list of output parameters. *)
      meth_vars: 'b creol_vardecl list;
	(** A list of local variables. *)
      meth_body: ('a, 'b) Statement.t option
	(** The method body. *)
    }





(** Abstract syntax of a with clause.

    A with clause consists of a co-interface name, a list of methods
    and a sequence of invariants. *)
module With: sig

  type ('a, 'b) t = {
    co_interface: string option;
    methods: ('a, 'b) creolmethod list;
    invariants: 'b Expression.t list
  }

end






module Class : sig

  type 'a inherits = string * ('a Expression.t list)

  type ('a, 'b) t =
      { name: string;
	parameters: 'b creol_vardecl list;
	inherits: 'b inherits list;
	contracts: string list;
	implements: string list;
	attributes: 'b creol_vardecl list;
	with_defs: ('a, 'b) With.t list }

end





module Interface : sig

  type ('a, 'b) t =
    { name: string;
      inherits: string list;
      with_decl: ('a, 'b) With.t option }

end





module Datatype : sig

  type ('a, 'b) t = {
    name: string
  }

end





module Exception : sig

  type 'b t = { name: string; parameters: 'b creol_vardecl list }

end




module Declaration : sig

  type ('a, 'b) t =
      Class of ('a, 'b) Class.t
      | Interface of ('a, 'b) Interface.t
      | Datatype of ('a, 'b) Datatype.t
      | Exception of 'b Exception.t

end





module Maude :
  sig
    type options = {
	mutable modelchecker: bool;
	mutable red_init: bool;
	mutable main: string option;
    }

    val of_creol: options -> out_channel -> ('a, 'b) Declaration.t list -> unit
  end




val pretty_print: out_channel -> ('a, 'b) Declaration.t list -> unit

val simplify: ('a, 'b) Declaration.t list -> ('a, 'b) Declaration.t list

val tailcall_successes : unit -> int

val optimise_tailcalls: ('a, 'b) Declaration.t list -> ('a, 'b) Declaration.t list

val find_definitions: (Note.t, 'a) Declaration.t list -> (Note.t, 'a) Declaration.t list
