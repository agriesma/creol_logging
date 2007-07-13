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

module Type =
  struct

    type note = {
      file: string;
      line: int
    }

    let make_note pos = {
      file = pos.Lexing.pos_fname ;
      line = pos.Lexing.pos_lnum
    }

    type t =
	Basic of note * string
	| Variable of note * string
	| Application of note * string * t list
	| Tuple of note * t list
	| Function of note * t list * t
	| Structure of note * field list
	| Variant of note * field list
	| Label of note * t * t list * t list
	| Intersection of note * t list
	| Union of note * t list
    and field =
	{ field_note: note;
	  field_name: string;
	  field_type: t
	}


    let note_of =
      function
	  Basic (n, _) -> n
	| Variable (n, _) -> n
	| Application (n, _, _) -> n
	| Tuple (n, _) -> n
	| Function (n, _, _) -> n
	| Structure (n, _) -> n
	| Variant (n, _) -> n
	| Label (n, _, _, _) -> n
	| Intersection (n, _) -> n
	| Union (n, _) -> n

    let file t = (note_of t).file

    let line t = (note_of t).line

    (* These are the support functions for the abstract syntax tree. *)

    let rec as_string =
      function
	  Basic (_, s) -> s
	| Variable (_, s) -> "`" ^ s
	| Application (_, s, p) ->
	    s ^ "[" ^ (string_of_creol_type_list p) ^ "]"
	| Tuple (_, p) ->
	    "[" ^ (string_of_creol_type_list p) ^ "]"
	| Function (_, d, r) ->
	    "[" ^ (string_of_creol_type_list d) ^ " -> " ^
		(as_string r) ^ "]"
	| Structure (_, f) -> "[# " ^ (string_of_field_list f) ^ " #]"
	| Variant (_, f) -> "[+ " ^ (string_of_field_list f) ^ " +]"
	| Intersection _ -> assert false (* XXX Implement if needed. *)
	| Union _ -> assert false (* XXX Implement if needed. *)
	| Label _ -> "/* Label */"
    and string_of_creol_type_list =
      function
	  [] -> ""
	| [t] -> as_string t
	| t::l -> (as_string t) ^ ", " ^ (string_of_creol_type_list l)
    and string_of_field_list =
      function
	  [f] -> string_of_field f
	| f::l -> (string_of_field f) ^ ", " ^ (string_of_field_list l)
	| [] -> assert false
    and string_of_field f = f.field_name ^ ": " ^ (as_string f.field_type)

  end

module Expression =
  struct

    type note = {
	file: string;
	line: int
    }
    
    let make_note pos = {
      file = pos.Lexing.pos_fname ;
      line = pos.Lexing.pos_lnum
    }

    type t =
	Null of note
	| Nil of note
	| Bool of note * bool
	| Int of note * int
	| Float of note * float
	| String of note * string
	| Id of note * string
        | StaticAttr of note * string * Type.t
	| Tuple of note * t list
	| ListLit of note * t list
	| SetLit of note * t list
        | FieldAccess of note * t * string
	| Unary of note * unaryop * t
	| Binary of note * binaryop * t * t
	| If of note * t * t * t
	| FuncCall of note * string * t list
	| Label of note * string
	| New of note * Type.t * t list
	| Extern of note * string
        | SSAId of note * string * int
        | Phi of note * t list
  and lhs =
          LhsVar of note * string
        | LhsAttr of note * string * Type.t
        | LhsWildcard of note * Type.t option
        | LhsSSAId of note * string * int
    and unaryop =
	Not
	| UMinus
	| Length
    and binaryop =
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

    (** Get the textual representation of a binary operator. *)
    let string_of_binaryop =
      function
	  Plus -> "+"
	| Minus -> "-"
	| Times -> "*"
	| Div -> "/"
	| Modulo -> "%"
	| Power -> "**"
	| Eq -> "="
	| Ne -> "/="
	| Le -> "<="
	| Lt -> "<"
	| Ge -> ">="
	| Gt -> ">"
	| And -> "&&"
	| Or -> "||"
	| Xor -> "^"
	| Implies -> "=>"
	| Iff -> "<=>"
	| Prepend -> "-|"
	| Append -> "|-"
	| Concat -> "|-|"
	| Project -> "\\"
	| In -> "in"

    (** Precedence of binary operators. *)
    let prec_of_binaryop =
      function
	  Plus -> (33, 33)
	| Minus -> (33, 33)
	| Times -> (31, 31)
	| Div -> (31, 31)
	| Modulo -> (31, 31)
	| Power -> (29, 29)
	| Eq -> (51, 51)
	| Ne -> (51, 51)
	| Le -> (37, 37)
	| Lt -> (37, 37)
	| Ge -> (37, 37)
	| Gt -> (37, 37)
	| In -> (53, 53)
	| And -> (55, 55)
	| Or -> (59, 59)
	| Xor -> (57, 57)
	| Implies -> (61, 61)
	| Iff -> (61, 61)
	| Prepend -> (33, 33)
	| Append -> (33, 33)
	| Concat -> (33, 33)
	| Project -> (35, 35)

    (** Get the textual representation of a unary operator *)
    let string_of_unaryop =
      function
	  Not -> "~"
	| UMinus -> "-"
	| Length -> "#"

    (** Return the precedence of a unary operator.  Only needed for pretty
	printing. *)
    let prec_of_unaryop =
      function
	  Not -> 53
	| UMinus -> 15
	| Length -> 15

    (** Extract the annotation of an expression *)
    let note =
      function
	  Null a -> a
	| Nil a -> a
	| Bool (a, _) -> a
	| Int (a, _) -> a
	| Float (a, _) -> a
	| String (a, _) -> a
	| Id (a, _) -> a
	| StaticAttr(a, _, _) -> a
	| Tuple (a, _) -> a
	| ListLit (a, _) -> a
	| SetLit (a, _) -> a
	| FieldAccess (a, _, _) -> a
	| Unary (a, _, _) -> a
	| Binary (a, _, _, _) -> a
	| If (a, _, _, _) -> a
	| FuncCall (a, _, _) -> a
	| Label (a, _) -> a
	| New (a, _, _) -> a
	| Extern(a, _) -> a

    let name =
      function
	  LhsVar(_, n) -> n
	| LhsAttr(_, n, _) -> n
	| LhsWildcard _ -> "_"

    (** Whether an expression contains a label *)
    let rec contains_label_p =
	function
	  Label _ -> true
	| Unary (_, _, e) -> contains_label_p e
	| Binary (_, _, e, f) -> (contains_label_p e) || (contains_label_p f)
	| If (_, c, t, f) -> (contains_label_p c) || (contains_label_p t) ||
	    (contains_label_p f)
	| FuncCall(_, _, args) ->
	    List.fold_left (fun a b -> a || (contains_label_p b)) false args
	| New (_, _, args) ->
	    List.fold_left (fun a b -> a || (contains_label_p b)) false args
	| _ -> false

    (** Whether an expression is a binary expression with a specific
        operator *)
    let binary_op_p op =
	function
	    Binary(_, o, _, _) when o = op -> true
	  | _ -> false

    (** Determines, whether a term is a boolean atom.

        An atom is either an atomic proposition or the negation of an
        atom.  Strictly speaking, only a and ~a are atoms, and not
	~~a or ~~~a, but we need not make this distinction. *)
    let rec atom_p =
        function
	    Unary(_, Not, e) -> atom_p e
          | Binary(_, (And|Or|Implies|Xor|Iff), _, _) -> false
	  | _ -> true

    (** Determines, whether a term is already in DNF *)
    let rec dnf_p =
	function
	    Unary(_, Not, e) -> not (dnf_p e)
	  | Binary(_, Or, e, f) -> 
		(dnf_p e) && (dnf_p f)
	  | Binary(_, (And|Implies|Xor|Iff), e, f) ->
		if not (dnf_p e) || not (dnf_p f) then false
		else not (binary_op_p Or e) && not (binary_op_p Or f)
	  | _ -> true

    (** Negate a boolean formula. *)
    let rec negate =
      function
	  Bool(b, v) -> Bool(b, not v)
	| Unary (b, Not, e) -> e
	| Binary(b, Eq, l, r) -> Binary(b, Ne, l, r)
	| Binary(b, Ne, l, r) -> Binary(b, Eq, l, r)
	| Binary (b, And, e, f) -> Binary (b, Or, negate e, negate f)
	| Binary (b, Or, e, f) -> Binary (b, And, negate e, negate f)
	| Binary (b, Implies, e, f) -> Binary (b, And, e, negate f)
	| Binary (b, Xor, e, f) -> Binary (b, Iff, e, f)
	| Binary (b, Iff, e, f) -> Binary (b, Xor, e, f)
	| e -> Unary (note e, Not, e)



    (** Rewrite a boolean expression to negation normal form (NNF).

	A formula is called in negation normal form, if and only if
	all negation operators are applied to atoms, and the only
	occuring binary connectives are [&&] and [||].  *)
    let rec to_nnf =
      function
	  Unary (b, Not, e) -> negate (to_nnf e)
        | Binary (b, And, e, f) -> Binary (b, And, to_nnf e, to_nnf f)
        | Binary (b, Or, e, f) -> Binary (b, Or, to_nnf e, to_nnf f)
        | Binary (b, Implies, e, f) ->
	    Binary (b, Or, negate (to_nnf e), to_nnf f)
        | Binary (b, Xor, e, f) ->
	    let ae = to_nnf e and af = to_nnf f in
	      Binary (b, Or, Binary (b, And, ae, negate af),
                     Binary (b, And, negate ae, af))
        | Binary (b, Iff, e, f) ->
	    let ae = to_nnf e and af = to_nnf f in
	      Binary (b, Or, Binary (b, And, ae, af),
                     Binary (b, And, negate ae, negate af))
	| e -> e

    (** Convert a boolean expression into {i conjunctive normal form}.

	The resulting formula may be exponentially longer.

        Assumes, that the expression is well-typed, that all operators
	have their standard meaning, and that the expression is {i
	not} lowered to Core Creol. *)
    let to_cnf f =
      let rec to_cnf_from_nnf =
	function
	    Binary (b, And, f, g) ->
	      Binary (b, And, to_cnf_from_nnf f, to_cnf_from_nnf g)
	  | FuncCall (b, "&&", [f; g]) ->
	      (* XXX: Should check that this is boolean *)
	      FuncCall (b, "&&", [to_cnf_from_nnf f; to_cnf_from_nnf g])
	  | Binary(b, Or, f, g) ->
	      (* Push or inside of and using distributive laws *)
	      let rec to_cnf_or left right =
		match (left, right) with
		    (Binary(lb, And, lf, lg), _) ->
		      Binary(b, And, to_cnf_or lf right, to_cnf_or lg right)
		  | (FuncCall (lb, "&&", [lf; lg]), _) ->
	      	      (* XXX: Should check that this is boolean *)
		      FuncCall (b, "&&", [to_cnf_or lf right; to_cnf_or lg right])
		  | (_, Binary(rb, And, rf, rg)) ->
		      Binary (b, And, to_cnf_or left rf, to_cnf_or left rg)
		  | (_, FuncCall (rb, "&&", [rf; rg])) ->
	      	      (* XXX: Should check that this is boolean *)
		      FuncCall (b, "&&", [to_cnf_or left rf; to_cnf_or left rg])
		  | _ ->
		      (* neither subformula contains and *)
		      Binary(b, Or, to_cnf_from_nnf f, to_cnf_from_nnf g)
	      in
		to_cnf_or f g
	  | FuncCall (b, "||", [f; g]) ->
	      (* Push or inside of and using distributive laws *)
	      let rec to_cnf_or left right =
		match (left, right) with
		    (Binary(lb, And, lf, lg), _) ->
		      Binary(b, And, to_cnf_or lf right, to_cnf_or lg right)
		  | (FuncCall (lb, "&&", [lf; lg]), _) ->
	      	      (* XXX: Should check that this is boolean *)
		      FuncCall (b, "&&", [to_cnf_or lf right; to_cnf_or lg right])
		  | (_, Binary(rb, And, rf, rg)) ->
		      Binary(b, And, to_cnf_or left rf, to_cnf_or left rg)
		  | (_, FuncCall (rb, "&&", [rf; rg])) ->
	      	      (* XXX: Should check that this is boolean *)
		      FuncCall (b, "&&", [to_cnf_or left rf; to_cnf_or left rg])
		  | _ ->
		      (* neither subformula contains and *)
		      FuncCall (b, "||", [to_cnf_from_nnf f; to_cnf_from_nnf g])
	      in
		to_cnf_or f g
	  | Binary (_, (Implies|Xor|Iff), _, _) ->
	      assert false (* Input was assumed to be in NNF *)
	  | FuncCall (_, ("=>" | "^" | "<=>"), [_; _]) ->
	      assert false (* Input was assumed to be in NNF *)
	  | e -> e
      in
	to_cnf_from_nnf (to_nnf f)

    (** Convert a boolean expression into {i disjunctive normal form}.

        Assumes, that the expression is well-typed, that all operators have
	their standard meaning, and that the expression is not lowered to
	Core Creol. *)
    let to_dnf exp =
      to_nnf (negate (to_cnf (to_nnf (negate exp))))

    (** Check whether all occurences of labels are positive in a formula
	f.  Assume, that a label value does not occur as the argument of
	a function call! *)
    let all_labels_positive_p expr =
      let rec all_labels_positive =
	(* Check whether all labels are positive assuming negation normal
	   form *)
        function
	    Unary (_, Not, Label _) -> false
	  | Binary(_, (And | Or), left, right) ->
	      (all_labels_positive left) && (all_labels_positive right)
	  | FuncCall(_, ("&&" | "||"), [left; right]) ->
	      (* XXX: Should check, whether the type is boolean. *)
	      (all_labels_positive left) && (all_labels_positive right)
	  | Binary(_, (Implies|Xor|Iff), f, g) ->
	      assert false (* Input was assumed to be in NNF *)
          | _ -> true
      in
	all_labels_positive (to_nnf expr)
  end

module Statement =
  struct
    type note = {
	file: string;
	line: int
    }
    
    let make_note pos = {
      file = pos.Lexing.pos_fname ;
      line = pos.Lexing.pos_lnum
    }


    type t =
	Skip of note
	| Release of note
	| Assert of note * Expression.t
	| Assign of note * Expression.lhs list * Expression.t list
	| Await of note * Expression.t
	| AsyncCall of note * string option * Expression.t * string *
	    Expression.t list
	| Reply of note * string * Expression.lhs list
	| Free of note * string
	| SyncCall of note * Expression.t * string *
	    Expression.t list * Expression.lhs list
	| AwaitSyncCall of note * Expression.t * string *
	    Expression.t list * Expression.lhs list
	| LocalAsyncCall of note * string option * string * string option *
	    string option * Expression.t list
	| LocalSyncCall of note * string * string option * string option *
            Expression.t list * Expression.lhs list
	| AwaitLocalSyncCall of note * string * string option * string option *
            Expression.t list * Expression.lhs list
	| Tailcall of note * string * string option * string option *
	    Expression.t list
	| If of note * Expression.t * t * t
	| While of note * Expression.t * Expression.t option *
	    t
	| Sequence of note * t  * t
	| Merge of note * t * t
	| Choice of note * t * t
        | Extern of note * string

    let note =
      function
	  Skip a -> a
	| Assert (a, _) -> a
	| Assign (a, _, _) -> a
	| Release a -> a
	| Await (a, _) -> a
	| AsyncCall (a, _, _, _, _) -> a
	| Reply (a, _, _) -> a
	| Free (a, _) -> a
	| SyncCall (a, _, _, _, _) -> a
	| AwaitSyncCall (a, _, _, _, _) -> a
	| LocalAsyncCall (a, _, _, _, _, _) -> a
	| LocalSyncCall (a, _, _, _, _, _) -> a
	| AwaitLocalSyncCall (a, _, _, _, _, _) -> a
	| Tailcall (a, _, _, _, _) -> a
	| If (a, _, _, _) -> a
	| While (a, _, _, _) -> a
	| Sequence(a, _, _) -> a
	| Merge(a, _, _) -> a
	| Choice(a, _, _) -> a
	| Extern(a, _) -> a

    let is_skip_p =
      (** Test, whether the statement is a skip statement. *)
      function
	Skip _ -> true
	| _ -> false

    let rec normalize_sequences stmt =
      (** Transform an arbitrary statement [stmt] into a statement in
	  which all sequences are right-threaded, i.e., the first (or
	  left) part of a sequence statement is always a non-sequence
	  statement. *)
      let rec append_to_sequence stm1 stm2 =
	(** Append the sequence of statement [stm2] to the sequence
	    [stm1].  Assumes that both statement sequences are
	    right-threaded. *)
	match stm1 with
	    Sequence(a, s1, s2) ->
	      Sequence(a, s1, append_to_sequence s2  stm2)
	  | _ -> Sequence (note stm1, stm1, stm2)
      in
	match stmt with
	    If (a, c, s1, s2) ->
	      If (a, c, normalize_sequences s1, normalize_sequences s2)
	  | While (a, c, i, s) -> 
	      While (a, c, i, normalize_sequences s)
	  | Sequence (a, (Sequence _ as s1), (Sequence _ as s2)) ->
	      append_to_sequence (normalize_sequences s1)
		(normalize_sequences s2)
	  | Sequence (a, Sequence (a1, s11, s12), s2) ->
	      Sequence (a, s11, normalize_sequences (Sequence (a1, s12, s2)))
	  | Sequence (a, s1, (Sequence _ as s2)) ->
	      Sequence (a, s1, normalize_sequences s2)
	  | Merge (a, s1, s2) ->
	      Merge (a, normalize_sequences s1, normalize_sequences s2)
	  | Choice (a, s1, s2) ->
	      Choice (a, normalize_sequences s1, normalize_sequences s2)
	  | _ -> stmt

  end

(** The abstract syntax of Creol *)

module VarDecl =
  struct
    type t =
      { name: string; var_type: Type.t; init: Expression.t option }
  end

module Method =
  struct
    type t =
      { meth_name: string;
        meth_inpars: VarDecl.t list;
        meth_outpars: VarDecl.t list;
        meth_vars: VarDecl.t list;
        meth_body: Statement.t option }
  end





module With = struct

  type t = {
    co_interface: string option;
    methods: Method.t list;
    invariants: Expression.t list
  }

end





module Class =
struct

  type inherits = string * Expression.t list

  type t =
      { name: string;
	parameters: VarDecl.t list;
	inherits: inherits list;
	contracts: string list;
	implements: string list;
	attributes: VarDecl.t list;
	with_defs: With.t list }

end





module Interface =
struct

  type  t =
      { name: string;
	inherits: string list;
	with_decl: With.t list }

end

module Exception =
struct
  type t = { name: string; parameters: VarDecl.t list }
end





module Operation =
  struct

    type t = {
      name: string;
      parameters: VarDecl.t list;
      result_type: Type.t;
      body: Expression.t
    }

  end


module Datatype =
  struct

    type t = {
      name: Type.t;
      supers: Type.t list;
      operations: Operation.t list
    }

  end





module Declaration =
struct

  type t =
      Class of Class.t
      | Interface of Interface.t
      | Datatype of Datatype.t
      | Exception of Exception.t

end


module Program =
  struct
    type t = Declaration.t list
  end
