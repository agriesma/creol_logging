(*i
 * Creol.ml -- Definition and manipulation of Creol AST
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
i*)

(*s Definition of the abstract syntax of Creol and a collection
    of functions for its manipulation.

*)


(** Types *)
module Type =
  struct

    type t =
	(** The abstract syntax of types in Creol. *)
	| Internal
	  (** The co-interface of internal calls *)
	| Basic of string
	  (** A basic type. *)
	| Variable of string
	    (** A type variable. *)
	| Application of string * t list
	    (** A type application, e.g., [List[Int]]. *)
	| Tuple of t list
	    (** The type of a tuple. *)
	| Intersection of t list
	    (** The type is an intersection type.  Intersection types
		do not have concrete syntax. Usually, an intersection
		type arises as the type of the expression {\c this},
		and in very rare circumstances during type inference. *)
	| Disjunction of t list
	    (** The type is an intersection type.  Intersection types
		do not have concrete syntax. Usually, an intersection
		type arises as the type of the expression {\c this},
		and in very rare circumstances during type inference. *)
	| Function of t * t
	    (** The type of a function.  This type does not have a concrete
		syntax, but is created during type checking. *)
    and field =
	(** The declaration of a field of a structure or a variant. *)
	{ field_name: string; (** Name of this field. *)
	  field_type: t (** Type of this field *)
	}

    let name =
      function
        Basic n -> n
      | Application (n, _) -> n
      | _ -> assert false

    let any = Basic "Any"

    let any_p t = (t = Basic "Any")

    let data = Basic "Data"

    let data_p t = (t = Basic "Data")

    let real = Basic "Real"

    let real_p t = (t = real)

    let int = Basic "Int"

    let int_p t = (t = int)

    let bool = Basic "Bool"

    let bool_p t = (t = bool)

    let string = Basic "String"

    let string_p t = (t = string)

    let history = Basic "Data"

    let history_p t = (t = history)

    let label l = Application ("Label", l)

    let list t = Application ("List", t)

    let variable_p =
      function
	  Variable _ -> true
	| _ -> false

    (* These are the support functions for the abstract syntax tree. *)

    let rec as_string =
      function
	  Basic s -> s
	| Variable s -> "`" ^ s
	| Application (s, []) ->
	    s ^ "[ ]"
	| Application (s, p) ->
	    s ^ "[" ^ (string_of_creol_type_list p) ^ "]"
	| Tuple p ->
	    "[" ^ (string_of_creol_type_list p) ^ "]"
	| Intersection l -> "/\\ [" ^ (string_of_creol_type_list l) ^ "]"
	| Disjunction l -> "\\/ [" ^ (string_of_creol_type_list l) ^ "]"
	| Function (s, t) -> "[" ^ (as_string s) ^ " -> " ^ (as_string t) ^ "]"
	| Internal -> "/* Internal */"
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

    let get_from_label =
      function
	  Application ("Label", args) -> args
	| _ -> assert false

    let rec occurs_p v =
      (** Check if a variable named [v] occurs in the argument type. *)
      function
	  Internal -> false
	| Basic _ -> false
	| Variable x -> v = x
	| Application (_, l) -> List.exists (occurs_p v) l
	| Tuple l -> List.exists (occurs_p v) l
	| Intersection l -> List.exists (occurs_p v) l
	| Disjunction l -> List.exists (occurs_p v) l
	| Function (s, t) -> (occurs_p v s) || (occurs_p v t)

    let rec sentence_p =
      (** Checks whether a type contains any (free) variables. *)
      function
	  Basic _ -> true
	| Variable _ -> false
	| Application (_, p) -> List.for_all sentence_p p
	| Tuple p -> List.for_all sentence_p p
	| Intersection l -> List.for_all sentence_p l
	| Disjunction l -> List.for_all sentence_p l
	| Function (s, t) -> (sentence_p s) && (sentence_p t)
	| Internal -> true

    let free_variables t =
      let rec compute res =
	function
	    Basic _ -> res
	  | Variable x -> if List.mem x res then res else x::res
	  | Application (_, p) -> List.fold_left (fun a -> compute a) res p
	  | Tuple p -> List.fold_left (fun a -> compute a) res p
	  | Intersection l -> List.fold_left (fun a -> compute a) res l
	  | Disjunction l -> List.fold_left (fun a -> compute a) res l
	  | Function (s, t) -> List.fold_left (fun a -> compute a) res [s; t]
	  | Internal -> res
      in
	  compute [] t

    (* Substitution module *)
    module Subst = Map.Make(String)
    type subst = t Subst.t

    let rec substitute v t =
      (** Substitute each occurence of a type variable called [v] by
	  the type [t] in the argument type. *)
      function
	  Internal -> Internal
	| Basic b -> Basic b
	| Variable x -> if x = v then t else Variable x
	| Application (c, l) -> Application(c, List.map (substitute v t) l)
	| Tuple l -> Tuple (List.map (substitute v t) l)
	| Intersection l -> Intersection (List.map (substitute v t) l)
	| Disjunction l -> Disjunction (List.map (substitute v t) l)
	| Function (d, r) -> Function (substitute v t d, substitute v t r)

    let rec apply_substitution s =
      function
	  Internal -> Internal
	| Basic b -> Basic b
	| Variable x ->
	    if Subst.mem x s then Subst.find x s else Variable x
	| Application (c, l) ->
	    Application(c, List.map (apply_substitution s) l)
	| Tuple l ->
	    Tuple (List.map (apply_substitution s) l)
	| Intersection l ->
	    Intersection (List.map (apply_substitution s) l)
	| Disjunction l ->
	    Disjunction (List.map (apply_substitution s) l)
	| Function (d, r) ->
	    Function (apply_substitution s d, apply_substitution s r)

    type signature = t * t list option * t list option

    let default_sig = (any, None, None)

    let co_interface (c, _, _) = c

    let domain (_, d, _) = d

    let range (_, _, r) = r

    let string_of_sig =
      function
	  (co, None, None) ->
	    "[ " ^ (as_string co) ^ " | unknown -> unknown ]"
	| (co, Some d, None) ->
	    "[ " ^ (as_string co) ^ " | " ^ (string_of_creol_type_list d) ^
	      " -> unknown ]"
	| (co, None, Some r) ->
	    "[ " ^ (as_string co) ^ " | unknown -> " ^
	      (string_of_creol_type_list r) ^ " ]"
	| (co, Some d, Some r) ->
	    "[ " ^ (as_string co) ^ " | " ^ (string_of_creol_type_list d) ^
	      " -> " ^ (string_of_creol_type_list r) ^ " ]"

  end

module Expression =
  struct

    type note = {
	file: string;
	line: int;
	ty: Type.t
    }

    let make_note pos =
      {
	file = pos.Lexing.pos_fname ;
	line = pos.Lexing.pos_lnum ;
	ty = Type.data
      }

    let typed_dummy_note t =
      { file = "**dummy**"; line = 0; ty = t }

    let dummy_note = typed_dummy_note Type.data

    let file note = note.file

    let line note = note.line

    let set_type note t = { note with ty = t }

    type t =
	  This of note
	| QualifiedThis of note * Type.t
	| Caller of note
	| Now of note
	| Null of note
	| Nil of note
	| History of note
	| Bool of note * bool
	| Int of note * int
	| Float of note * float
	| String of note * string
	| Id of note * string
        | StaticAttr of note * string * Type.t
	| Tuple of note * t list
	| ListLit of note * t list
	| SetLit of note * t list
	| Unary of note * unaryop * t
	| Binary of note * binaryop * t * t
	| FuncCall of note * string * t list
	| If of note * t * t * t
	| Label of note * t
	| New of note * Type.t * t list
(*i	| Choose of note * string * Type.t * t
	| Forall of note * string * Type.t * t
	| Exists of note * string * Type.t * t i*)
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
	| Wedge
	| Or
	| Vee
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
	| Wedge -> "/\\"
	| Or -> "||"
	| Vee -> "\\/"
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
	| Le | Lt | Ge | Gt -> (37, 37)
	| In -> (53, 53)
	| And | Wedge -> (55, 55)
	| Or | Vee -> (59, 59)
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
	  This a -> a
	| QualifiedThis (a, _) -> a
	| Caller a -> a
	| Now a -> a
	| Null a -> a
	| Nil a -> a
	| History a -> a
	| Bool (a, _) -> a
	| Int (a, _) -> a
	| Float (a, _) -> a
	| String (a, _) -> a
	| Id (a, _) -> a
	| StaticAttr(a, _, _) -> a
	| Tuple (a, _) -> a
	| ListLit (a, _) -> a
	| SetLit (a, _) -> a
	| Unary (a, _, _) -> a
	| Binary (a, _, _, _) -> a
	| If (a, _, _, _) -> a
	| FuncCall (a, _, _) -> a
	| Label (a, _) -> a
	| New (a, _, _) -> a
(*i	| Choose (a, _, _, _) -> a
	| Forall (a, _, _, _) -> a
	| Exists (a, _, _, _) -> a i*)
	| Extern (a, _) -> a
	| SSAId (a, _, _) -> a
	| Phi (a, _) -> a

    let get_type expr = (note expr).ty

    let get_lhs_type =
      function
	  LhsVar(n, _) -> n.ty
	| LhsAttr(n, _, _) -> n.ty
	| LhsWildcard (n, _) -> n.ty
	| LhsSSAId (n, _, _) -> n.ty

    let name =
      function
	  LhsVar(_, n) -> n
	| LhsAttr(_, n, _) -> n
	| LhsWildcard _ -> "_"
	| LhsSSAId (_, n, _) -> n

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
	  | FuncCall (b, "&&", [f; g]) when Type.bool_p b.ty ->
	      FuncCall (b, "&&", [to_cnf_from_nnf f; to_cnf_from_nnf g])
	  | Binary(b, Or, f, g) ->
	      (* Push or inside of and using distributive laws *)
	      let rec to_cnf_or left right =
		match (left, right) with
		    (Binary(lb, And, lf, lg), _) ->
		      Binary(b, And, to_cnf_or lf right, to_cnf_or lg right)
		  | (FuncCall (lb, "&&", [lf; lg]), _) when Type.bool_p b.ty ->
		      FuncCall (b, "&&", [to_cnf_or lf right; to_cnf_or lg right])
		  | (_, Binary(rb, And, rf, rg)) ->
		      Binary (b, And, to_cnf_or left rf, to_cnf_or left rg)
		  | (_, FuncCall (rb, "&&", [rf; rg])) when Type.bool_p b.ty ->
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
		  | (FuncCall (lb, "&&", [lf; lg]), _) when Type.bool_p b.ty ->
		      FuncCall (b, "&&", [to_cnf_or lf right; to_cnf_or lg right])
		  | (_, Binary(rb, And, rf, rg)) ->
		      Binary(b, And, to_cnf_or left rf, to_cnf_or left rg)
		  | (_, FuncCall (rb, "&&", [rf; rg])) when Type.bool_p b.ty ->
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
	  | FuncCall(n, ("&&" | "||"), [left; right]) when Type.bool_p n.ty ->
	      (all_labels_positive left) && (all_labels_positive right)
	  | Binary(_, (Implies|Xor|Iff), f, g) ->
	      assert false (* Input was assumed to be in NNF *)
          | _ -> true
      in
	all_labels_positive (to_nnf expr)
  end

module Statement =
  struct

    open Expression

    module IdSet = Set.Make(String)

    type note = {
	file: string;
	line: int;
	life: IdSet.t
    }

    let file note = note.file

    let line note = note.line

    let dummy_note =
      { file = "**dummy**"; line = 0; life = IdSet.empty }

    let make_note pos = {
      file = pos.Lexing.pos_fname ;
      line = pos.Lexing.pos_lnum ;
      life = IdSet.empty 
    }

    type t =
      (** Abstract syntax of statements in Creol.  The type parameter ['a]
	  refers to the type of possible annotations. *)
	Skip of note
	| Release of note
	| Assert of note * Expression.t
	| Prove of note * Expression.t
	| Assign of note * Expression.lhs list * Expression.t list
	  (** A multiple assignment statement.  Requires that the two lists
	      are of the same length. *)
	| Await of note * Expression.t
	| Posit of note * Expression.t
	  (** A posit statement, which is used to define {i true} properties
              about time in a model. *)
	| AsyncCall of note * Expression.lhs option * Expression.t * string *
	   Type.signature *  Expression.t list
	| Reply of note * Expression.t * Expression.lhs list
	| Free of note * Expression.lhs list
	| Bury of note * Expression.lhs list
	    (** Bury represents a special form of assignment, setting all
		its arguments to null.  It does not affect life ranges
		of its arguments and assumes that all argument names are
		already dead at that position. *)
	| SyncCall of note * Expression.t * string * Type.signature *
	    Expression.t list * Expression.lhs list
	| AwaitSyncCall of note * Expression.t * string * Type.signature *
	    Expression.t list * Expression.lhs list
	| LocalAsyncCall of note * Expression.lhs option * string *
	    Type.signature * string option * string option * Expression.t list
	| LocalSyncCall of note * string * Type.signature * string option *
	    string option * Expression.t list * Expression.lhs list
	| AwaitLocalSyncCall of note * string * Type.signature * string option *
	    string option * Expression.t list * Expression.lhs list
	| Tailcall of note * string * Type.signature * string option *
	    string option * Expression.t list
	| If of note * Expression.t * t * t
	| While of note * Expression.t * Expression.t option *
	    t
	| Sequence of note * t  * t
	| Merge of note * t * t
	| Choice of note * t * t
        | Extern of note * string

    let note = function
	| Skip a | Assert (a, _) | Prove (a, _) | Assign (a, _, _)
	| Release a | Await (a, _) | Posit (a, _)
	| AsyncCall (a, _, _, _, _, _) | Reply (a, _, _)
	| Free (a, _) | Bury (a, _)
	| SyncCall (a, _, _, _, _, _)
	| AwaitSyncCall (a, _, _, _, _, _)
	| LocalAsyncCall (a, _, _, _, _, _, _)
	| LocalSyncCall (a, _, _, _, _, _, _)
	| AwaitLocalSyncCall (a, _, _, _, _, _, _)
	| Tailcall (a, _, _, _, _, _)
	| If (a, _, _, _) | While (a, _, _, _)
	| Sequence (a, _, _) | Merge (a, _, _) | Choice (a, _, _)
	| Extern (a, _) -> a

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

    let simplify_assignment =
      function
          Assign (note, lhs, rhs) ->
            let needed =
	      function
	          (LhsVar (a, v), Id (b, w)) when v = w -> false
                | _ -> true
            in
	    begin
	      match List.split (List.filter needed (List.combine lhs rhs)) with
	          ([], []) -> Skip note
	        | (nl, nr) -> Assign (note, nl, nr)
	      end
        | _ -> assert false

    let rec remove_redundant_skips =
      function
	  (Release _ | Assert _ | Prove _ | Assign _ | Await _ | Posit _ |
	   AsyncCall _ | Reply _ | Free _ | Bury _ | SyncCall _ |
	   AwaitSyncCall _ | LocalAsyncCall _ | LocalSyncCall _ | 
	   AwaitLocalSyncCall _ | Tailcall _ | Extern _) as s -> s
	| Skip note -> Skip note
	| If (note, c, t, f) ->
	    If (note, c, remove_redundant_skips t, remove_redundant_skips f)
	| While (note, c, i, b) -> While (note, c, i, remove_redundant_skips b)
	| Sequence (_, Skip note, Skip _) -> Skip note
	| Sequence (_, Skip _, stmt) -> remove_redundant_skips stmt
	| Sequence (_, stmt, Skip _) -> remove_redundant_skips stmt
	| Sequence (note, stmt1, stmt2) -> 
	    Sequence (note, remove_redundant_skips stmt1,
		     remove_redundant_skips stmt2)
	| Merge (note, l, r) -> Merge (note, l, r)
	| Choice (note, l, r) -> Choice (note, l, r)

    let assignment_of_bury =
      function
	  Bury (a, (_::_ as l)) ->
	    let null v =
	      let t = Expression.get_lhs_type v in
		Expression.Null (Expression.typed_dummy_note t) in
	      Assign (a, l, List.map null l)
	| _ -> assert false
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
      { name: string;
        coiface: Type.t;
        inpars: VarDecl.t list;
        outpars: VarDecl.t list;
        vars: VarDecl.t list;
        body: Statement.t option;
	location: string
	  (** The class or interface in which this method
	      declaration/definition is defined.  We use the fact that
	      body = None for interfaces only to distinguish the name
	      spaces. *)
	}

    let make_decl n inp outp =
      { name = n; coiface = Type.Internal; inpars = inp; outpars = outp;
	vars = []; body = None; location = "" }

    let set_cointerface cf m = { m with coiface = cf }

    let build_type l =
	Type.Tuple (List.map (fun v -> v.VarDecl.var_type) l)

    let domain_type m = build_type m.inpars

    let range_type m = build_type m.outpars

    let find_variable meth name =
      let find l = List.find (fun { VarDecl.name = n } -> n = name) l in
      try
	find meth.vars
      with
	  Not_found ->
	    try
	      find meth.inpars
	    with
		Not_found -> find meth.outpars

  end





(** Abstract syntax of a with clause.

    A with clause consists of a co-interface name, a list of methods
    and a sequence of invariants. *)

module With = struct

  type t = {
    co_interface: Type.t;
    methods: Method.t list;
    invariants: Expression.t list
  }

end


module Inherits =
  struct
    type t = string * Expression.t list
  end



module Class =
struct

  type t =
      { name: string;
	parameters: VarDecl.t list;
	inherits: Inherits.t list;
	contracts: Inherits.t list;
	implements: Inherits.t list;
	attributes: VarDecl.t list;
	with_defs: With.t list;
	hidden: bool;
	file: string;
	line: int }

  let get_type cls =
    match List.map fst (cls.implements @ cls.contracts) with
	[] -> Type.any
      | [t] -> Type.Basic t
      | i -> Type.Intersection (List.map (fun t -> Type.Basic t) i)

  let find_attr_decl cls name =
    let find l = List.find (function { VarDecl.name = n } -> n = name) l
    in
      try
	find cls.attributes
      with
	  Not_found -> find cls.parameters


end





module Interface =
struct

  type  t =
      { name: string;
	inherits: Inherits.t list;
	with_decls: With.t list;
	hidden: bool }

end

module Exception =
struct
  type t = { name: string; parameters: VarDecl.t list; hidden: bool }
end





module Function =
  struct

    type t = {
      name: string;
      parameters: VarDecl.t list;
      result_type: Type.t;
      body: Expression.t;
      hidden: bool
    }

    let domain_type o =
      Type.Tuple (List.map (fun v -> v.VarDecl.var_type) o.parameters)

  end


module Datatype =
  struct

    type t = {
      name: Type.t;
      supers: Type.t list;
      hidden: bool
	(** Hide from output.  Set for datatypes defined in the prelude. *)
    }

  end





module Declaration =
struct

  type t =
      Class of Class.t
      | Interface of Interface.t
      | Datatype of Datatype.t
      | Exception of Exception.t
      | Function of Function.t

  let hide =
    function
	Class c -> Class { c with Class.hidden = true }
      | Interface i -> Interface { i with Interface.hidden = true }
      | Datatype d -> Datatype { d with Datatype.hidden = true }
      | Exception e -> Exception { e with Exception.hidden = true }
      | Function f -> Function { f with Function.hidden = true }

end


module Program =
  struct

    (* The type of a program.  This is currently just a list of
       declarations. *)
    type t = Declaration.t list

    (* Generally, if a class or an interface is not found in the
       program, we raise a \ocwupperid{Not\_found} exception.  But if
       the context of the class or the interface is known, one of the
       two following exceptions is raised. *)
    exception Class_not_found of string * int * string

    exception Interface_not_found of string * int * string


    (* Find a class of name \ocwlowerid{name} in
       \ocwlowerid{program}. This function raises
       \ocwupperid{Not\_found} if no class has the name
       \ocwlowerid{name} in the program. *)
    let find_class ~program ~name =
      let class_with_name =
	function
	    Declaration.Class { Class.name = n } -> n = name
	  | _ -> false
      in
	match List.find class_with_name program with
	    Declaration.Class cls -> cls
	  | _ -> assert false


    (* Find all super-classes of a class \ocwlowerid{name} in
       \ocwlowerid{program}.  Raises a \ocwupperid{Class\_not\_found}
       exception in the context of the class from which the class is
       supposed to be inherited. A \ocwupperid{Not\_found} exception
       is raised if \ocwlowerid{name} does not exist in the
       program. *)
    let superclasses ~program name =
      let rec fold cls =
	List.fold_left (fun a (n, _) -> a@(work cls n)) [] cls.Class.inherits
      and work super n =
	let cls =
	  try
	    find_class program n
	  with
	      Not_found ->
		raise (Class_not_found (super.Class.file ,
				       super.Class.line, n))
	in
	  fold cls
      in
	fold (find_class program name)


    let subclass_p ~program s t =
      (** Return true if [s] is a subclass of [t] *)
      let rec search s =
	(s = t) ||
	  try
	    let s' = find_class program s in
	      (List.exists (fun u -> search u) (List.map fst s'.Class.inherits))
	  with
	      Not_found -> false
      in search s


    let find_interface ~program ~name =
      let interface_with_name =
	function
	    Declaration.Interface { Interface.name = n } when n = name -> true
	  | _ -> false
      in
	match List.find interface_with_name program with
	    Declaration.Interface i -> i
	  | _ -> assert false

    let subinterface_p ~program s t =
      (** Return true if [s] is a subinterface of [t] *)
      if t = "Any" then
	(* Everything is a sub-interface of [Any] *)
	true
      else
	let rec search s =
	  (s = t) ||
	    try
	      let s' = find_interface program s in
	        (List.exists (fun u -> search u) (List.map fst s'.Interface.inherits))
	    with
	        Not_found -> false
	in
	  search s

  let contracts_p program cls iface =
    (** Return true if the class [cls] contracts the interface [iface] *)
    if iface = Type.any then
      true
    else
      let p i = subinterface_p program i (Type.as_string iface) in
        List.exists p (List.map fst cls.Class.contracts)
  
    let find_datatype ~program ~name =
      let datatype_with_name =
	function
	    Declaration.Datatype { Datatype.name = Type.Basic n }
	      when n = name -> true
	  | Declaration.Datatype { Datatype.name = Type.Application (n, _) }
	      when n = name -> true
	  | _ -> false
      in
	match List.find datatype_with_name program with
	    Declaration.Datatype d -> d
	  | _ -> assert false

    let rec sub_datatype_p program s t =
      (** Return true if s is a sub-datatype of [t] *)
      try
	let s_decl =
	  find_datatype program s
	in
	  (s = t) ||
	    (List.exists (function u -> sub_datatype_p program u t)
		(List.map Type.as_string s_decl.Datatype.supers))
      with
	  Not_found -> false

    let find_functions ~program ~name =
      (** Find all definitions of functions called [name] in
	  [program], whose formal parameters are compatible with
	  [domain].  Only return the most specific matches.  Returns
	  the empty list if none is found. *)
      let f a =
	function
	    Declaration.Function f when f.Function.name  = name -> f::a
	  | _ -> a
      in
        List.fold_left f [] program

    let rec find_attr_decl program cls name =
      let rec find lst =
	match lst with
	    [] -> raise Not_found
	  | i::r ->
	      try
		find_attr_decl program (find_class program (fst i)) name
	      with
		  Not_found -> find r
      in
	try
	  Class.find_attr_decl cls name
	with
	    Not_found -> find cls.Class.inherits

    (* Return a list of all interfaces which are implemented by a
       class.  These interfaces are either directly claimed to be
       implemented, contracted by the class itself, or contracted by
       one of the super classes. *)
    let class_implements ~program cls =
      let rec work result =
	function
	    [] -> result
	  | (n, _)::l when List.mem n result -> work result l
	  | (n, _)::l ->
	      let i =
		try
		  find_interface program n
		with 
		    Not_found ->
		      raise (Interface_not_found
				(cls.Class.file, cls.Class.line, n))
	      in
		work (n::result) (l@i.Interface.inherits)
      in
      let rec contracts cls =
	let f a (n, _) = a@(contracts (find_class program n)) in
	  List.fold_left f cls.Class.contracts cls.Class.inherits
      in
	work [] ((contracts cls) @ cls.Class.implements)


    let rec subtype_p program s t =
      (** Decides whether [s] is a subtype of [t] in [program]. *)
      match (s, t) with
	  (_, Type.Basic "Data") when Type.sentence_p s ->
	    true (* Everything type of kind * is a subtype of data *)
	| (_, _) when s = t -> true (* Every type is a subtype of itself *)
	| (Type.Basic st, Type.Basic tt) ->
	    (sub_datatype_p program st tt) || (subinterface_p program st tt)
	| (_, Type.Intersection l) ->
	    List.for_all (subtype_p program s) l
	| (_, Type.Disjunction l) ->
	    List.exists (subtype_p program s) l
	| (Type.Application (sc, sa), Type.Application (tc, ta)) ->
	    (sc = tc) &&
	      begin
		try 
		  List.for_all2 (subtype_p program) sa ta
		with
		    Invalid_argument _ -> false
	      end
	| (Type.Application _, _) -> assert false (* But see above *)
	| (Type.Tuple sa, Type.Tuple ta) ->
	    begin
	     try 
		(List.for_all2 (subtype_p program) sa ta)
	      with
		  Invalid_argument _ -> false
	    end
	| (Type.Tuple _, _) -> assert false (* But see above *)
	| (Type.Intersection sa, _) ->
	    List.exists (fun s -> subtype_p program s t) sa
	| (Type.Disjunction sa, _) ->
	    List.for_all (fun s -> subtype_p program s t) sa
	| (Type.Internal, Type.Internal) -> true
	| ((Type.Internal, _) | (_, Type.Internal)) -> false
	| (Type.Function (d1, r1), Type.Function (d2, r2)) -> 
	    (subtype_p program d1 d2) && (subtype_p program r2 r1)
	| (Type.Function _, _) -> assert false (* But see above *)
	| (Type.Variable _, _) -> assert false (* But see reflexivity above *)
	| (Type.Basic _, _) -> assert false (* But see above *)


    (* Return the greates lower bound of all types in [lst] in
       [program], i.e., a type t with (lower-bound) t <: s for all s
       in [lst] and with (maximality) s <: t for all types s with s
       <: u for some u in [lst].

       Formally, the greatest lower bound of an empty [lst] is the top
       type.

       The result may be an intersection types, which is caused by
       classes implementing multiple interfaces.  If this function
       returns an intersection, the solution is ambigous.  *)
    let meet ~program lst =
      let find_meet s t =
	if subtype_p program s t then
	  s
	else if subtype_p program t s then
	  t
	else
	  Type.data
      in
	match lst with
	    [] -> Type.data
	  | hd::tl -> List.fold_left find_meet hd tl


    (* Return the least upper bound of all types in [lst] in
       [program], i.e., a type t with (upper-bound) s <: t for all s
       in [lst] and with (minimality) t <: s for all types s with u
       <: s for some u in [lst].

       Formally, the least upper bound of an empty [lst] is the bottom
       type.  However, bottom need not exist, and the function will
       therefore fail.

       The result may be an intersection types, which is caused by
       classes implementing multiple interfaces.  If this function
       returns an intersection, the solution is ambigous.  *)
    let join ~program lst =
      let find_join s t =
	if subtype_p program s t then
	  t
	else
	  s
      in
	match lst with
	    [] -> assert false
	  | hd::tl -> List.fold_left find_join hd tl


    let find_method_in_with ~program ~name ~signature w =
      let (coiface, ins, outs) = signature in
      let dom = match ins with None -> Type.data | Some t -> Type.Tuple t in
      let rng = match outs with None -> Type.data | Some t -> Type.Tuple t in
      let p m =
	m.Method.name = name &&
	  (subtype_p program dom (Method.domain_type m)) &&
	  (subtype_p program (Method.range_type m) rng)
      in
	List.filter p w.With.methods


    (* Find all definitions of a method called [name] that matches the
       signature [(coiface, inputs, outputs)] in [iface] and its
       super-interfaces.  *)
    let interface_find_methods ~program ~iface ~name (coiface, ins, outs) =
      let rec find_methods_in_interface i =
        let q w = subtype_p program coiface w.With.co_interface in
        let withs = List.filter q i.Interface.with_decls in
        let here =
	  List.fold_left
	    (fun a w -> (find_method_in_with program name (coiface, ins, outs) w)@a) [] withs
        and supers = List.map fst i.Interface.inherits
        in
	  List.fold_left
            (fun r i ->
              (find_methods_in_interface (find_interface program i))@r)
            here supers
      in
	find_methods_in_interface iface

    let interface_provides_p ~program ~iface ~meth signature =
      (** Check whether the interface [iface] or one of its
	  superinterfaces provide a method matching the signature
	  [(coiface, inputs, outputs)]. *)
      [] <> (interface_find_methods program iface meth signature)

    let class_find_methods ~program ~cls ~name (coiface, ins, outs) =
      (** Find all definitions of a method called [name] that matches
	  the signature [(coiface, inputs, outputs)] in class [cls]
	  and its super-classes.  *)
      let rec find_methods_in_class c =
	let q w = subtype_p program coiface w.With.co_interface in
	let withs = List.filter q c.Class.with_defs in
	let here =
	  List.fold_left (fun a w -> (find_method_in_with program name (coiface, ins, outs) w)@a) [] withs
        and supers = List.map fst c.Class.inherits
        in
	  List.fold_left
            (fun r i ->
              (find_methods_in_class (find_class program i))@r)
            here supers
      in
	find_methods_in_class cls

    let class_provides_method_p ~program ~cls meth signature =
      [] <> (class_find_methods program cls meth signature)

  end
