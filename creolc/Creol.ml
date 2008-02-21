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

(* Types *)
module Type =
struct

  type t =
      | Internal
      | Basic of string
      | Variable of string
      | Application of string * t list
      | Tuple of t list
      | Intersection of t list
      | Disjunction of t list
      | Function of t * t

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

  let time = Basic "Time"

  let time_p t = (t = time)

  let history = Basic "Data"

  let history_p t = (t = history)

  let label l = Application ("Label", l)

  let label_p t = match t with Application("Label", _) -> true | _ -> false

  let list t = Application ("List", t)

  let list_p t = match t with Application("List", _) -> true | _ -> false

  let set t = Application ("Set", t)

  let set_p t = match t with Application("Set", _) -> true | _ -> false

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

  let get_from_label =
    function
	Application ("Label", args) -> args
      | _ -> assert false


  (* Check if a variable named [v] occurs in the argument type. *)
  let rec occurs_p v =
    function
	Internal -> false
      | Basic _ -> false
      | Variable x -> v = x
      | Application (_, l) -> List.exists (occurs_p v) l
      | Tuple l -> List.exists (occurs_p v) l
      | Intersection l -> List.exists (occurs_p v) l
      | Disjunction l -> List.exists (occurs_p v) l
      | Function (s, t) -> (occurs_p v s) || (occurs_p v t)

  (* Checks whether a type contains any (free) variables. *)
  let rec sentence_p =
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


  (* Substitute each occurence of a type variable called [v] by the
     type [t] in the argument type. *)
  let rec substitute v t =
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

  let default_sig ?(coiface = None) (): signature =
    let t = match coiface with None -> any | Some c -> c in (t, None, None)

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


(* Define the abstract syntax of a name of a variable or an
   attribute. This module defines a linear order on these names.  *)
module Name =
struct

  type t =
      | Id of string
      | Attr of string * Type.t
      | Wildcard of Type.t option
      | SSAId of string * int

  let compare x y = assert false

end


module Expression =
struct

  type note = {
    file: string;
    line: int;
    ty: Type.t
  }

  let make_note ?(file = "**dummy**") ?(line = 0) ?(ty = Type.data) () =
    { file = file ; line = line ; ty = ty }

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
      | Int of note * Big_int.big_int
      | Float of note * Num.num
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
      | Choose of note * string * Type.t * t
      | Forall of note * string * Type.t * t
      | Exists of note * string * Type.t * t
      | Extern of note * string
      | SSAId of note * string * int
      | Phi of note * t list
  and lhs =
      LhsId of note * string
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

  (* Get the textual representation of a binary operator. *)
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

  (* Precedence of binary operators. *)
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

  (* Get the textual representation of a unary operator *)
  let string_of_unaryop =
    function
	Not -> "~"
      | UMinus -> "-"
      | Length -> "#"

  (* Return the precedence of a unary operator.  Only needed for
     pretty printing. *)
  let prec_of_unaryop =
    function
	Not -> 53
      | UMinus -> 15
      | Length -> 15

  (* Extract the annotation of an expression *)
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
      | Choose (a, _, _, _) -> a
      | Forall (a, _, _, _) -> a
      | Exists (a, _, _, _) -> a 
      | Extern (a, _) -> a
      | SSAId (a, _, _) -> a
      | Phi (a, _) -> a

  let get_type expr = (note expr).ty

  let set_note note =
    function
	This _ -> This note
      | QualifiedThis (_, t) -> QualifiedThis (note, t)
      | Caller _ -> Caller note
      | Now _ -> Now note
      | Null _ -> Null note
      | Nil _ -> Nil note
      | History _ -> History note
      | Bool (_, v) -> Bool (note, v)
      | Int (_, v) -> Int (note, v)
      | Float (_, v) -> Float (note, v)
      | String (_, v) -> String (note, v)
      | Id (_, i) -> Id (note, i)
      | StaticAttr(_, i, t) -> StaticAttr (note, i, t)
      | Tuple (_, l) -> Tuple (note, l)
      | ListLit (_, l) -> ListLit (note, l)
      | SetLit (_, l) -> SetLit (note, l)
      | Unary (_, o, a) -> Unary (note, o, a)
      | Binary (_, o, l, r) -> Binary (note, o, l, r)
      | If (_, c, t, f) -> If (note, c, t, f)
      | FuncCall (_, f, a) -> FuncCall (note, f, a)
      | Label (_, l) -> Label (note, l)
      | New (_, c, a) -> New (note, c, a)
      | Choose (_, v, t, p) -> Choose (note, v, t, p)
      | Forall (_, v, t, p) -> Forall (note, v, t, p)
      | Exists (_, v, t, p) -> Exists (note, v, t, p)
      | Extern (_, i) -> Extern (note, i)
      | SSAId (_, i, n) -> SSAId (note, i, n)
      | Phi (_, l) -> Phi (note, l)

  let get_lhs_type =
    function
	LhsId(n, _) -> n.ty
      | LhsAttr(n, _, _) -> n.ty
      | LhsWildcard (n, _) -> n.ty
      | LhsSSAId (n, _, _) -> n.ty

  (* Extract the annotation of an expression *)
  let variable =
    function
        Id (_, n) -> n
      | StaticAttr (_, n, _) -> n
      | SSAId (_, n, _) -> n
      | _ -> assert false

  let name =
    function
	LhsId(_, n) -> n
      | LhsAttr(_, n, _) -> n
      | LhsWildcard _ -> "_"
      | LhsSSAId (_, n, _) -> n


  (* Whether an expression is a true literal. *)
  let rec literal_p =
    function
      | Null _ | Nil _ | Bool _ | Int _ | Float _ | String _ ->
	  true
      | Tuple (_, l) | ListLit (_, l) | SetLit (_, l) ->
	  List.for_all literal_p l
      | _ ->
	  false


  (* Whether an expression is a constant expression. *)
  let rec constant_p =
    function
	This _ | QualifiedThis _ | Caller _ -> true
      | Now _ -> true (* At least within the same state *)
      | Null _ | Nil _ -> true
      | History _ -> true (* At least within the same state *)
      | Bool _ | Int _ | Float _ | String _ -> true
      | Id _ -> false
      | StaticAttr _ -> false
      | Tuple (_, l) -> List.for_all constant_p l
      | ListLit (_, l) -> List.for_all constant_p l
      | SetLit (_, l) -> List.for_all constant_p l
      | Unary (_, _, a) -> constant_p a
      | Binary (_, _, l, r) -> (constant_p l) && (constant_p r)
      | If (_, c, t, f) -> (constant_p c) && (constant_p t) && (constant_p f)
      | FuncCall (_, _, a) -> List.for_all constant_p a
      | Label _ -> false
      | New _ -> false
      | Choose _ -> false
      | Forall (_, _, _, p) -> constant_p p
      | Exists (_, _, _, p) -> constant_p p
      | Extern (_, i) -> false
      | SSAId _ -> false
      | Phi _ -> false

  (* Whether an expression contains a label *)
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

  (* Whether an expression is a binary expression with a specific
     operator *)
  let binary_op_p op =
    function
	Binary(_, o, _, _) when o = op -> true
      | _ -> false

  (* Apply a type substitution to an expression. *)

  let rec substitute_types_in_expression subst expr =
    let subst_in_note note =
      { note with ty = Type.apply_substitution subst note.ty }
    in
      match expr with
	  This n ->
	    This (subst_in_note n)
	| QualifiedThis (n, t) ->
	    QualifiedThis (subst_in_note n, Type.apply_substitution subst t)
	| Caller n ->
	    Caller (subst_in_note n)
	| Null n ->
	    Null (subst_in_note n)
	| Nil n ->
	    Nil (subst_in_note n)
	| History n ->
	    Nil (subst_in_note n)
	| Now n ->
	    Now (subst_in_note n)
	| Bool (n, value) ->
	    Bool (subst_in_note n, value)
	| Int (n, value) ->
	    Int (subst_in_note n, value)
	| Float (n, value) ->
	    Float (subst_in_note n, value)
	| String (n, value) ->
	    String (subst_in_note n, value)
	| Tuple (n, l) ->
	    Tuple (subst_in_note n,
		   List.map (substitute_types_in_expression subst) l)
	| ListLit (n, l) ->
	    ListLit (subst_in_note n,
		     List.map (substitute_types_in_expression subst) l)
	| SetLit (n, l) ->
	    SetLit (subst_in_note n,
		    List.map (substitute_types_in_expression subst) l)
	| Id (n, name) ->
	    Id (subst_in_note n, name)
	| StaticAttr (n, name, t) ->
	    StaticAttr (subst_in_note n, name, t)
	| Unary (n, op, arg) ->
	    Unary (subst_in_note n, op,
		   substitute_types_in_expression subst arg)
	| Binary (n, op, arg1, arg2) ->
	    Binary (subst_in_note n, op,
		    substitute_types_in_expression subst arg1,
		    substitute_types_in_expression subst arg2)
	| FuncCall (n, name, args) ->
	    FuncCall (subst_in_note n, name,
		      List.map (substitute_types_in_expression subst) args)
	| If (n, cond, iftrue, iffalse) ->
	    If (subst_in_note n,
		substitute_types_in_expression subst cond,
		substitute_types_in_expression subst iftrue,
		substitute_types_in_expression subst iffalse)
	| Label (n, l) ->
	    Label (subst_in_note n,
		   substitute_types_in_expression subst l)
	| New (n, t, args) ->
	    New (subst_in_note n, Type.apply_substitution subst t,
		 List.map (substitute_types_in_expression subst) args)
	| Choose (n, i, t, e) ->
	    Choose (subst_in_note n, i,
		    Type.apply_substitution subst t,
		    substitute_types_in_expression subst e)
	| Forall (n, i, t, e) ->
	    Forall (subst_in_note n, i,
		    Type.apply_substitution subst t,
		    substitute_types_in_expression subst e)
	| Exists (n, i, t, e) ->
	    Exists (subst_in_note n, i,
		    Type.apply_substitution subst t,
		    substitute_types_in_expression subst e)
	| Extern _ as e -> e
	| SSAId (n, name, version) ->
	    SSAId (subst_in_note n, name, version)
	| Phi (n, args) ->
	    Phi (subst_in_note n,
		 List.map (substitute_types_in_expression subst) args)


  (* Determines, whether a term is a boolean atom.

     An atom is either an atomic proposition or the negation of an
     atom.  Strictly speaking, only a and ~a are atoms, and not
     ~~a or ~~~a, but we need not make this distinction. *)
  let rec atom_p =
    function
	Unary(_, Not, e) -> atom_p e
      | Binary(_, (And|Or|Implies|Xor|Iff), _, _) -> false
      | _ -> true

  (* Determines, whether a term is already in DNF *)
  let rec dnf_p =
    function
	Unary(_, Not, e) -> not (dnf_p e)
      | Binary(_, Or, e, f) -> 
	  (dnf_p e) && (dnf_p f)
      | Binary(_, (And|Implies|Xor|Iff), e, f) ->
	  if not (dnf_p e) || not (dnf_p f) then false
	  else not (binary_op_p Or e) && not (binary_op_p Or f)
      | _ -> true

  (* Negate a boolean formula. *)
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



  (* Rewrite a boolean expression to negation normal form (NNF).

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

  (* Convert a boolean expression into {i conjunctive normal form}.

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

  (* Convert a boolean expression into {i disjunctive normal form}.

     Assumes, that the expression is well-typed, that all operators have
     their standard meaning, and that the expression is not lowered to
     Core Creol. *)
  let to_dnf exp = to_nnf (negate (to_cnf (to_nnf (negate exp))))

  (* Check whether all occurences of labels are positive in a formula
     f.  Assume, that a label value does not occur as the argument
     of a function call! *)
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

  (*s Convert a an identifier set to a string. *)

  let string_of_idset s =
    let rec work =
      function
	  [] -> ""
	| [e] -> e
	| e::l -> e ^ ", " ^ (work l)
    in
      "{" ^ (work (IdSet.elements s)) ^ "}"


  (* A definition of the note attached to a statement. *)

  type note = {
    file: string;
    line: int;
    def: IdSet.t;
    life: IdSet.t;
  }

  let make_note ?(file = "**dummy**") ?(line = 0) () = {
    file = file;
    line = line;
    def = IdSet.empty;
    life = IdSet.empty;
  }


  (* Abstract syntax of statements in Creol. *)
  type t =
      Skip of note
    | Release of note
    | Assert of note * Expression.t
    | Prove of note * Expression.t
    | Assign of note * Expression.lhs list * Expression.t list
	(* A multiple assignment statement.  Requires that the two lists
	   are of the same length. *)
    | Await of note * Expression.t
    | Posit of note * Expression.t
	(* A posit statement, which is used to define {i true} properties
           about time in a model. *)
    | AsyncCall of note * Expression.lhs option * Expression.t * string *
	Type.signature *  Expression.t list
    | Reply of note * Expression.t * Expression.lhs list
    | Free of note * Expression.lhs list
    | Bury of note * Expression.lhs list
	(* Bury represents a special form of assignment, setting all
	   its arguments to null.  It does not affect life ranges
	   of its arguments and assumes that all argument names are
	   already dead at that position. *)
    | SyncCall of note * Expression.t * string * Type.signature *
	Expression.t list * Expression.lhs list
    | AwaitSyncCall of note * Expression.t * string * Type.signature *
	Expression.t list * Expression.lhs list
    | LocalAsyncCall of note * Expression.lhs option * string *
	Type.signature * string option * string option * Expression.t list
	(* The optional [lhs] expression represents the value of the
	   name of the variable in which the label is stored.  The
	   following argument is the name of the method.  Then comes the
	   [signature].  The first optional string is the name of a class
	   and denotes the \emph{upper} bound for searching the method
	   body.  The next term represents the corresponding \emph{lower}
	   bound.

	   The term \emph{upper bound} in this context means, that the
	   implementation must be defined in a subclass of the given
	   class \texttt{C}, written \texttt{<:C}.

	   The term \emph{lower bound} in this context means, that the
	   implementation must be defined in a superclass of the given
	   class \texttt{C}, written \texttt{:>C}. *)
    | LocalSyncCall of note * string * Type.signature * string option *
	string option * Expression.t list * Expression.lhs list
    | AwaitLocalSyncCall of note * string * Type.signature * string option *
	string option * Expression.t list * Expression.lhs list
    | Tailcall of note * string * Type.signature * string option *
	string option * Expression.t list
    | If of note * Expression.t * t * t
    | While of note * Expression.t * Expression.t * t
    | DoWhile of note * Expression.t * Expression.t * t
    | Sequence of note * t  * t
    | Merge of note * t * t
    | Choice of note * t * t
    | Extern of note * string


  (* Test, whether the statement is a skip statement. *)
  let skip_p =
    function
	Skip _ -> true
      | _ -> false


  (* Extract the note from a statement. *)
  let note =
    function
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
      | If (a, _, _, _) | While (a, _, _, _) | DoWhile (a, _, _, _)
      | Sequence (a, _, _) | Merge (a, _, _) | Choice (a, _, _)
      | Extern (a, _) -> a


  let file stmt = (note stmt).file
  
  let line stmt = (note stmt).line

  (* Set the note of a statement *)
  let set_note stmt n =
    match stmt with
      | Skip _ -> Skip n
      | Assert (_, e) -> Assert (n, e)
      | Prove (_, e) -> Prove (n, e)
      | Assign (_, vs, es) -> Assign (n, vs, es)
      | Release _ -> Release n
      | Await (_, c) -> Await (n, c)
      | Posit (_, c) -> Posit (n, c)
      | AsyncCall (_, l, x, m, s, i) -> AsyncCall (n, l, x, m, s, i)
      | Reply (_, l, vs) -> Reply (n, l, vs)
      | Free (_, ls) -> Free (n, ls)
      | Bury (_, vs) -> Bury (n, vs)
      | SyncCall (_, x, m, s, i, o) -> SyncCall (n, x, m, s, i, o)
      | AwaitSyncCall (_, x, m, s, i, o) -> AwaitSyncCall (n, x, m, s, i, o)
      | LocalAsyncCall (_, lab, m, s, l, u, i) ->
	  LocalAsyncCall (n, lab, m, s, l, u, i)
      | LocalSyncCall (_, m, s, l, u, i, o) ->
          LocalSyncCall (n, m, s, l, u, i, o)
      | AwaitLocalSyncCall (_, m, s, l, u, i, o) ->
          AwaitLocalSyncCall (n, m, s, l, u, i, o)
      | Tailcall (_, a, b, c, d, e) -> Tailcall (n, a, b, c, d, e)
      | If (_, c, s1, s2) -> If (n, c, s1, s2)
      | While (_, c, i, s) -> While (n, c, i, s)
      | DoWhile (_, c, i, s) -> DoWhile (n, c, i, s)
      | Sequence (_, s1, s2) -> Sequence (n, s1, s2)
      | Merge (_, s1, s2) -> Merge (n, s1, s2)
      | Choice (_, s1, s2) -> Choice (n, s1, s2)
      | Extern (_, s) -> Extern(n, s)


  (* Give a string representation of a statement *)
  let to_string =
    function
      | Skip _ -> "skip"
      | Assert (_, _) -> "assert _"
      | Prove (_, _) -> "prove _"
      | Assign (_, _, _) -> "_ := _"
      | Release _ -> "release"
      | Await (_, _) -> "await _"
      | Posit (_, _) -> "release _"
      | AsyncCall (_, _, _, _, _, _) -> " _!_._(_)"
      | Reply (_, _, _) -> "_?(_)"
      | Free (_, _) -> "free _"
      | Bury (_, _) -> "bury _"
      | SyncCall (_, _, _, _, _, _) -> "_._(_;_)"
      | AwaitSyncCall (_, _, _, _, _, _) -> "await _._(_;_)"
      | LocalAsyncCall (_, _, _, _, _, _, _) -> "_!_<:_:>_(_)"
      | LocalSyncCall (_, _, _, _, _, _, _) -> "_<:_:>_(_;_)"
      | AwaitLocalSyncCall (_, _, _, _, _, _, _) -> "await _<:_:>_(_;_)"
      | Tailcall (_, _, _, _, _, _) -> "tailcall _<:_:>_(_)"
      | If (_, _, _, _) -> "if _ then _ else _ end"
      | While (_, _, _, _) -> "while _ do _ end"
      | DoWhile (_, _, _, _) -> "do _ while _"
      | Sequence (_, _, _) -> "_;_"
      | Merge (_, _, _) -> "_|||_"
      | Choice (_, _, _) -> "_[]_"
      | Extern (_, s) -> "extern \"" ^ s ^ "\""


  (* Get the variables defined at a statement.

     In case of a sequence of statements, return the set of variables
     of the final statement.  For a [Sequence] statement, the
     invariant is, that a variable is defined if it is defined at its
     final statement. *)
  let def s = (note s).def


  (* Set the variables defined at a statement. *)
  let set_def s d =
    let note' = { (note s) with def = d } in set_note s note'


  (* Check whether a variable is defined for a statement. *)
  let def_p s v =
    IdSet.mem v (def s)


  (* Get the variables life at a statement. *)
  let life s = (note s).life


  (* Set the variables life at a statement. *)
  let set_life s l =
    let note' = { (note s) with life = l } in set_note s note'


  (* Check whether a variable is life at a statement. *)
  let life_p stmt v = IdSet.mem v (life stmt)


  (* Transform an arbitrary statement [stmt] into a statement in which
     all sequences are right-threaded, i.e., the first (or left)
     part of a sequence statement is always a non-sequence
     statement. *)
  let rec normalize_sequences stmt =
    (* Append the sequence of statement [stm2] to the sequence [stm1].
       Assumes that both statement sequences are right-threaded. *)
    let rec append_to_sequence stm1 stm2 =
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
	| DoWhile (a, c, i, s) -> 
	    DoWhile (a, c, i, normalize_sequences s)
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
	        (LhsId (a, v), Id (b, w)) when v = w -> false
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
      | DoWhile (note, c, i, b) ->
	  DoWhile (note, c, i, remove_redundant_skips b)
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
	  let nul v =
	    let t = Expression.get_lhs_type v in
	      Expression.Null (Expression.make_note ~ty:t ()) in
	    Assign (a, l, List.map nul l)
      | _ -> assert false
end

(* The abstract syntax of Creol *)

module VarDecl =
  struct
    type t =
      { name: string; var_type: Type.t; init: Expression.t option }
  end

module Method =
  struct

   (* Abstract syntax tree node of a method declaration or method definition.
      If [body] is [None], then the node represents a declaration.  If it
      is not [None], the node represents a method definition.

      The member [location] indicates the class or interface in which this
      method declaration or definition is defined.  The fact that
      [body = None] is used to distinguish class names from interface
      names.  *)

    type t =
      { name: string;
        coiface: Type.t;
        inpars: VarDecl.t list;
        outpars: VarDecl.t list;
	requires: Expression.t;
	ensures: Expression.t;
        vars: VarDecl.t list;
        body: Statement.t option;
	location: string
      }

    (* This is the empty method.  It is used by the type checker
       for checking types on class level expressions. *)

    let empty =
      { name = ""; coiface = Type.Internal; inpars = []; outpars = [];
	requires = Expression.Bool(Expression.make_note (), true);
	ensures = Expression.Bool(Expression.make_note (), true);
	vars = []; body = None; location = "" }

    let make_decl n inp outp r e =
      { name = n; coiface = Type.Internal; inpars = inp; outpars = outp;
	requires = r; ensures = e; vars = []; body = None; location = "" }

    let set_cointerface cf m = { m with coiface = cf }


    (* Internal helper function to build a type signature from a list
       [l] of variable declarations. *)

    let build_type l =
      Type.Tuple (List.map (fun v -> v.VarDecl.var_type) l)

    let domain_type m = build_type m.inpars

    let range_type m = build_type m.outpars

    (* Build a method signature type from the declaration. *)
    let signature m: Type.signature =
      (m.coiface,
      Some (List.map (fun v -> v.VarDecl.var_type) m.inpars),
      Some (List.map (fun v -> v.VarDecl.var_type) m.outpars))


    (* String representation of a method name. *)

    let name_as_string meth =
      meth.location ^ "::" ^ meth.name ^ (Type.string_of_sig (signature meth))
      

    (* This predicate holds if the method is a definition of the init
       method. *)
    let init_p =
      function
	  { name = "init"; coiface = Type.Internal; inpars = [];
            outpars = []; body = Some _ } -> true
	| _ -> false

    (* This predicate holds if the method is a definition of the run
       method. *)
    let run_p =
      function
	  { name = "run"; coiface = Type.Internal; inpars = [];
            outpars = []; body = Some _ } -> true
	| _ -> false


    (* Find the declaration of the variable [name] by first searching
       the local attributes, then searching the input parameters and
       finally searching the output paramenters.  Raises [Not_found]
       if the variable is not found. *)
    let find_variable ~meth name =
      let p { VarDecl.name = n } = (n = name) in
	try
	  List.find p meth.vars
	with
	    Not_found ->
	      try
		List.find p meth.inpars
	      with
		  Not_found -> List.find p meth.outpars


    (* Determine whether a local variable is a label. *)
    let label_p ~meth name =
      Type.label_p (find_variable meth name).VarDecl.var_type


    (* Determine whether [name] is the name of an input parameter to
       [meth]. *)
    let input_p meth name =
      List.exists (fun { VarDecl.name = n } -> n = name) meth.inpars

    (* Determine whether [name] is the name of an output parameter to
       [meth]. *)
    let output_p meth name =
      List.exists (fun { VarDecl.name = n } -> n = name) meth.outpars

    (* Indicate whether the variable [name] is local to the method. *)
    let var_p meth name =
      List.exists (fun { VarDecl.name = n } -> n = name) meth.vars

    (* Indicate whether the variable [name] is local to the method,
       i.e., defined as a local attribute, an input parameter, or an
       output parameter. *)
    let local_p meth name =
      var_p meth name || input_p meth name || output_p meth name

    let apply_to_body (f: Statement.t -> Statement.t) meth =
      match meth.body with
	  None ->
	    meth
	| Some body ->
	    { meth with body = Some (f body) }

  end





(* Abstract syntax of a with clause.

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

  let has_attr_p ~cls ~name =
    let f l = List.exists (function { VarDecl.name = n } -> n = name) l in
      (f cls.attributes) || (f cls.parameters)

  let find_attr_decl ~cls ~name =
    let find l = List.find (function { VarDecl.name = n } -> n = name) l
    in
      try
	find cls.attributes
      with
	  Not_found ->
	    find cls.parameters


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
      (* Hide from output.  Set for datatypes defined in the prelude. *)
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


  let show =
    function
	Class c -> Class { c with Class.hidden = false }
      | Interface i -> Interface { i with Interface.hidden = false }
      | Datatype d -> Datatype { d with Datatype.hidden = false }
      | Exception e -> Exception { e with Exception.hidden = false }
      | Function f -> Function { f with Function.hidden = false }

end


(*s Defines an abstract syntax of a program. *)

module Program =
struct

  (* The type of a program.  This is currently just a list of
     declarations. *)

  type t = Declaration.t list


  (* Generally, if a class or an interface is not found in the
     program, a [Not_found] exception is raised.  But if the context
     of the class or the interface is known, one of the two following
     exceptions is raised. *)

  exception Class_not_found of string * int * string

  exception Interface_not_found of string * int * string


  (* Take a list [l] of declarations and make a program structure out
     of it. *)

  let make l = l


  (* Find a class of name [name] in [program]. This function raises
     [Not_found] if no class has the name [name] in the program. *)
  let find_class ~program ~name =
    let class_with_name =
      function
	  Declaration.Class { Class.name = n } -> n = name
	| _ -> false
    in
      match List.find class_with_name program with
	  Declaration.Class cls -> cls
	| _ -> assert false

  (* Get the type of a class. *)

  let type_of_class ~program ~name =
    Class.get_type (find_class program name)



  (* Find all super-classes of a class [name] in [program].  Raises a
     [Class_not_found] exception in the context of the class from
     which the class is supposed to be inherited. A [Not_found]
     exception is raised if [name] does not exist in the program. *)

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


  (* Return true if [s] is a subclass of [t]. *)

  let subclass_p ~program s t =
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
	  Declaration.Interface { Interface.name = n } -> name = n
	| _ -> false
    in
      match List.find interface_with_name program with
	  Declaration.Interface i -> i
	| _ -> assert false


  (* Check, whether [iface] is an interface in [program] *)

  let interface_p ~program ~iface =
    match iface with
	Type.Internal -> true
      | Type.Basic n ->
	  let p =
	    function
		Declaration.Interface { Interface.name = n' } -> n = n'
	      | _ -> false
	  in
	    List.exists p program
      | _ -> false


  (* Return true if [s] is a subinterface of [t]. *)

  let subinterface_p ~program s t =
    if t = "Any" then (* Everything is a sub-interface of [Any]. *)
      true
    else
      let rec search s =
	(s = t) ||
	  try
	    let s' = find_interface program s in
	      (List.exists (fun u -> search u)
		 (List.map fst s'.Interface.inherits))
	  with
	      Not_found -> false
      in
	search s


  (* Return true if the class [cls] contracts the interface [iface]. *)

  let contracts_p program cls iface =
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


  (* Return true if [s] is a sub-datatype of [t] *)

  let rec sub_datatype_p program s t =
    try
      let s_decl =
	find_datatype program s
      in
	(s = t) ||
	  (List.exists (function u -> sub_datatype_p program u t)
	     (List.map Type.as_string s_decl.Datatype.supers))
    with
	Not_found -> false


  (* Check, whether [ty] is a type in [program]. *)

  let type_p ~program ~ty =
    let p name' =
      function
          Declaration.Interface { Interface.name = n } -> (name' = n)
        | Declaration.Datatype { Datatype.name = t } -> (name' = (Type.name t))
	| _ -> false
    in
    let rec work_p =
      function 
	| Type.Internal ->
	    true
	| Type.Basic n ->
	    List.exists (p n) program
	| Type.Variable _ ->
	    true
	| Type.Application (n, a) ->
	    (List.exists (p n) program) && (List.for_all work_p a)
	| Type.Tuple l ->
	    List.for_all work_p l
	| Type.Intersection l ->
	    List.for_all work_p l
	| Type.Disjunction l ->
	    List.for_all work_p l
	| Type.Function (d, r) ->
	    (work_p d) && (work_p r)
    in
      work_p ty


  (* Find all definitions of functions called [name] in [program],
     whose formal parameters are compatible with [domain].  Only
     return the most specific matches.  Returns the empty list if none
     is found. *)

  let find_functions ~program ~name =
    let f a =
      function
	  Declaration.Function f when f.Function.name  = name -> f::a
	| _ -> a
    in
      List.fold_left f [] program


  (* Find the class declaration for an attribute. [cls] is the class
     in which we search for the attribute. [name] is the name of the
     attribute. *)
  let find_class_of_attr ~program ~cls ~attr =
    let rec work c =
      if Class.has_attr_p c attr then
	Some c
      else
	search c.Class.inherits
    and search =
      function
	  [] -> None
	| i::r ->
	    match work (find_class program (fst i)) with
		None -> search r
	      | cls' -> cls'
    in
      match work cls with
	  None -> raise Not_found
	| Some cls' -> cls'

  let find_attr_decl ~program ~cls ~name =
    let c = find_class_of_attr program cls name in
      Class.find_attr_decl c name


  (* Return a list of all interfaces which are implemented by a class.
     These interfaces are either directly claimed to be implemented,
     contracted by the class itself, or contracted by one of the
     super classes. *)

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

(* Compute the interface of a class, i.e., the set of all method it
   implements. We call this interface the \emph{full descriptor.} *)

  let full_class_descriptor ~program ~cls =
    []


(* Decides whether [s] is a subtype of [t] in [program]. *)

  let subtype_p ~program s t =
    let rec work =
      function 
	  (_, Type.Basic "Data") when Type.sentence_p s -> true 
	| (_, _) when s = t -> true
	| (Type.Basic st, Type.Basic tt) ->
	    (sub_datatype_p program st tt) || (subinterface_p program st tt)
	| (_, Type.Intersection l) ->
	    List.for_all (fun t -> work (s, t)) l
	| (_, Type.Disjunction l) ->
	    List.exists (fun t -> work (s, t)) l
	| (Type.Application (sc, sa), Type.Application (tc, ta)) ->
	    (sc = tc) &&
	      begin
		try 
		  List.for_all2 (fun s t -> work (s, t)) sa ta
		with
		    Invalid_argument _ -> false
	      end
	| (Type.Application _, _) -> assert false (* But see above *)
	| (Type.Tuple sa, Type.Tuple ta) ->
	    begin
	      try 
		(List.for_all2 (fun s t -> work (s, t)) sa ta)
	      with
		  Invalid_argument _ -> false
	    end
	| (Type.Tuple _, _) -> assert false (* But see above *)
	| (Type.Intersection sa, _) ->
	    List.exists (fun s -> work (s, t)) sa
	| (Type.Disjunction sa, _) ->
	    List.for_all (fun s -> work (s, t)) sa
	| (Type.Internal, Type.Internal) -> true
	| ((Type.Internal, _) | (_, Type.Internal)) -> false
	| (Type.Function (d1, r1), Type.Function (d2, r2)) -> 
	    (work (d1, d2)) && (work (r2, r1))
	| (Type.Function _, _) -> assert false
	| (Type.Variable _, _) -> assert false
	| (Type.Basic _, _) -> assert false
    in
      work (s, t)


  (* Return the greates lower bound of all types in [lst] in
     [program], i.e., a type $t$ with (lower-bound) $t <: s$ for all
     $s$ in [lst] and with (maximality) $s <: t$ for all types $s$
     with $s <: u$ for some $u$ in [lst].

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


  (* Return the least upper bound of all types in [lst] in [program],
     i.e., a type $t$ with (upper-bound) $s <: t$ for all $s$ in
     [lst] and with (minimality) $t <: s$ for all types $s$ with $u
     <: s$ for some $u$ in [lst].

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
     signature [(coiface, ins, outs)] in [iface] and its
     super-interfaces.  *)

  let interface_find_methods ~program ~iface ~name (coiface, ins, outs) =
    let rec find_methods_in_interface i =
      let q w = subtype_p program coiface w.With.co_interface in
      let withs = List.filter q i.Interface.with_decls in
      let here =
	List.fold_left
	  (fun a w ->
	     (find_method_in_with program name (coiface, ins, outs) w)@a)
	  [] withs
      and supers = List.map fst i.Interface.inherits
      in
	List.fold_left
          (fun r i ->
             (find_methods_in_interface (find_interface program i))@r)
          here supers
    in
      find_methods_in_interface iface


  (* Check whether the interface [iface] or one of its
     superinterfaces provide a method matching the [signature]. *)

  let interface_provides_p ~program ~iface ~meth signature =
    [] <> (interface_find_methods program iface meth signature)


  (* Find all definitions of a method called [name] that matches the
     signature [(coiface, ins, outs)] in class [cls] and its
     super-classes.  *)

  let class_find_methods ~program ~cls ~name (coiface, ins, outs) =
    let rec find_methods_in_class c =
      let q w = subtype_p program coiface w.With.co_interface in
      let withs = List.filter q c.Class.with_defs in
      let here =
	List.fold_left
	  (fun a w ->
	     (find_method_in_with program name (coiface, ins, outs) w)@a)
	  [] withs
      and supers = List.map fst c.Class.inherits
      in
	List.fold_left
          (fun r i ->
             (find_methods_in_class (find_class program i))@r)
          here supers
    in
      find_methods_in_class cls


  (* Check whether the class [cls] or one of its superclasses provide
     a method called [meth] matching the [signature]. *)

  let class_provides_method_p ~program ~cls meth signature =
    [] <> (class_find_methods program cls meth signature)

  (* This is the type of the subtype relation. *)

  module Rng = Set.Make(String)

  module Rel = Map.Make(String)

  (* Compute the transitive closure of the subtype relation. *)

  let transitive_closure rel =
    let rec do_it r =
      let f s = Rng.fold (fun elt acc -> Rng.union (Rel.find elt r) acc) s s in
      let r' = Rel.fold (fun key elt acc -> Rel.add key (f elt) acc) r r in
	if Rel.equal Rng.equal r r' then
	  r
	else
	  do_it r'
    in
      do_it rel

  (* Test whether the type relation is acyclic_p *)

  let cycle rel =
    let f key elt acc = if (Rng.mem key elt) then Rng.add key acc else acc in
      Rel.fold f rel Rng.empty

  let acyclic_p rel = Rng.is_empty (cycle rel)

  let rec string_of_cycle =
    function
	[] -> assert false
      | [s] -> s
      | s::r -> s ^ " <: " ^ (string_of_cycle r)


  (* Find a cycle.  This is using depth first search. *)

  let find_cycle ~program rel =
    let rec build (res: string list) (current: string) =
      let supers: string list =
	try
	  List.map Type.name (find_datatype program current).Datatype.supers ;
	with
	    Not_found ->
	      List.map fst (find_interface program current).Interface.inherits 
      in
	search (current::res) supers
    and search (res: string list) =
      function
	| [] -> res
	| cand::r when not (List.mem cand res) -> 
	    let res' = build res cand in
	      if List.mem cand res' then res' else search res r
	| cand::r -> cand::res
    in
      build [] (Rng.choose (cycle rel))


  (* Compute the subtype relation-ship of the program. *)

  let compute_subtype_relation program =
    let f rel =
      function
	| Declaration.Interface { Interface.name = name; inherits = supers } ->
	    Rel.add name
	      (List.fold_left (fun a (n, _) -> Rng.add n a) Rng.empty supers)
	      rel
	| Declaration.Datatype { Datatype.name = name; supers = supers } ->
	    Rel.add (Type.name name)
	      (List.fold_left (fun a n -> Rng.add (Type.name n) a)
                Rng.empty supers)
	      rel
	| _ -> rel
    in
      transitive_closure (List.fold_left f Rel.empty program)


  (* Apply a function to each method defined in the program. *)

  let for_each_method program f =
    let for_class c =
      let for_with_def w =
	{ w with With.methods =
	    List.map (fun m -> f program c m) w.With.methods }
      in
	{ c with Class.with_defs =
	    List.map for_with_def c.Class.with_defs }
    in
    let for_decl d =
      match d with
	  Declaration.Class c -> Declaration.Class (for_class c)
	| Declaration.Interface _ -> d
	| Declaration.Exception _ -> d
	| Declaration.Datatype _ -> d
	| Declaration.Function _ -> d
    in
      List.map for_decl program

end
 
