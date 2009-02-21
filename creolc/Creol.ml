(*
 * Creol.ml -- Definition and manipulation of Creol AST
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007, 2008 by Marcel Kyas
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
 *)


(** Definition of the abstract syntax of Creol and a collection
    of functions for its manipulation. *)


(** A set of identifiers (variable names, class names, interface names,
    ...) *)
module IdSet = Set.Make(String)


(** A map from identifiers (variable names, class names, interface
    names, ...).  *)
module IdMap = Map.Make(String)


(** This module defines the abstract syntax of types.

    The relation between types is not inherent to the types
    themselves, but they are defined by the program.  Therefore,
    functions relating types are defined in the {!Creol.Program}
    module.  *)
module Type =
struct

  (** Import the type of sets of variable names. *)
  module Vars = Set.Make(String)

  (** Values of type [t] represent types of Creol programs.

      [Internal] is the default type for [this].

      [Basic t] represents a basic type named [t]

      [Variable t] represents a type variable named [t]

      [Application (s,t)] represents the instantiation of a
      parameterised type [s] with the types [t].

      [Tuple t] represents the tuple type of types [t].

      [Intersection t] represents the intersection of types [t].
      Values of this type are instances of all types of [t].  

      [Disjunction t] represents the disjunction of types [t].  Values
      of this type are instances of some type of [t].  

      [Function (s,t)] represents the type of a function from values
      of type [s] to values of type [t]. *)
  type t =
    | Internal
    | Basic of string
    | Variable of string
    | Application of string * t list
    | Future of t list
    | Tuple of t list
    | Intersection of t list
    | Disjunction of t list
    | Function of t * t

  (** [name t] is the name of a type, if the type has a unique
      name. Raises [Failure "Type name"] if the type has no name. *)
  let rec name =
    function
      | Basic n | Application (n, _) -> n
      | Intersection [t] | Disjunction [t] -> name t
      | _ -> raise (Failure "Type name")

  (** The type {i Data}. *)
  let data = Basic "Data"

  (** The predicate [data_p t] is true, if the type [t] is the type {i
      Data}. *)
  let data_p t = (t = data)

  (** The type {i Any}. *)
  let any = Basic "Any"

  (** The predicate [any_p t] is true, if the type [t] is the type {i
      Any}. *)
  let any_p t = (t = any)

  (** The type {i Bool}. *)
  let bool = Basic "Bool"
    
  (** The predicate [bool_p t] is true, if the type [t] is the type {i
      Bool}. *)
  let bool_p t = (t = bool)

  (** The type {i Int}. *)
  let int = Basic "Int"

  (** The predicate [int_p t] is true, if the type [t] is the type {i
      Int}. *)
  let int_p t = (t = int)

  (** The type {i Float}. *)
  let float = Basic "Float"

  (** The predicate [float_p t] is true, if the type [t] is the type
      {i Float}. *)
  let float_p t = (t = float)

  (** The type {i String}. *)
  let string = Basic "String"

  (** The predicate [string_p t] is true, if the type [t] is the type
      {i String}. *)
  let string_p t = (t = string)

  (** The type {i Time}. *)
  let time = Basic "Time"

  (** The predicate [time_p t] is true, if the type [t] is the type {i
      Time}. *)
  let time_p t = (t = time)

  (** The type of a {i Future} of values of type [l]. *)
  let future l = Future l

  (** The predicate [future_p t] is true, if the type [t] is the type
      of a {i Future}. *)
  let future_p t = match t with Future _ -> true | _ -> false

  (** Make a term representing a {i List} of [t]. *)
  let list t = Application ("List", [t])

  (** The predicate [list_p t] is true, if the type [t] is the type of
      {i List\[a\]} for some type {i a}. *)
  let list_p t = match t with Application("List", [_]) -> true | _ -> false

  (** Make a term representing a {i Set} of [t]. *)
  let set t = Application ("Set", [t])

  (** The predicate [set_p t] is true, if the type [t] is the type of
      {i Set\[a\]} for some type {i a}. *)
  let set_p t = match t with Application("Set", [_]) -> true | _ -> false

  (** The predicate [collection_p] holds for all types [t] that are
      suitable as callees in multi-cast statements. *)
  let collection_p t = (list_p t) || (set_p t)

  (** Make a term representing a {i Set} of [t]. *)
  let map s t = Application ("Map", [s; t])

  (** The predicate [set_p t] is true, if the type [t] is the type of
      {i Set\[a\]} for some type {i a}. *)
  let map_p t = match t with Application("Map", [_; _]) -> true | _ -> false

  (** The type {i History}. *)
  let history = Basic "History"

  (** The predicate [history_p t] is true, if the type [t] is the type
      {i History}. *)
  let history_p t = (t = history)

  (** The predicate [variable_p t] holds, if [t] is a type
      variable. *)
  let variable_p =
    function
	Variable _ -> true
      | _ -> false

  (** Represent a type [t] as a string [string_of_type t]. *)
  let rec string_of_type =
    function
	Basic s -> s
      | Variable s -> "`" ^ s
      | Application (s, []) -> s ^ "[ ]"
      | Application (s, p) -> s ^ "[" ^ (string_of_type_list p) ^ "]"
      | Future p -> "Label" ^ "[" ^ (string_of_type_list p) ^ "]"
      | Tuple p -> "[" ^ (string_of_type_list p) ^ "]"
      | Intersection l -> "/\\ [" ^ (string_of_type_list l) ^ "]"
      | Disjunction l -> "\\/ [" ^ (string_of_type_list l) ^ "]"
      | Function (s, t) ->
	  "[" ^ (string_of_type s) ^ " -> " ^ (string_of_type t) ^ "]"
      | Internal -> "/* Internal */"
  (** Represent a list of types [l] as a string [string_of_type_list l]. *)
  and string_of_type_list =
    function
	[] -> ""
      | l -> String.concat ", " (List.map string_of_type l)

  (** Returns the type of the future. *)
  let type_of_future =
    function
	Future args -> args
      | _ -> assert false


  (** [free_variables t] is the set of all freely occurring variables in
      [t]. *)
  let free_variables t =
    let rec compute a =
      function
	  Basic _ -> a
	| Variable v -> Vars.add v a
	| Application (_, l) -> List.fold_left compute a l
	| Future l -> List.fold_left compute a l
	| Tuple l -> List.fold_left compute a l
	| Intersection l -> List.fold_left compute a l
	| Disjunction l -> List.fold_left compute a l
	| Function (s, t) -> List.fold_left compute a [s; t]
	| Internal -> a
    in
      compute Vars.empty t


  (** [occurs_p v t] checks if a type variable named [v] occurs in the
      argument type [t]. *)
  let occurs_p v t = Vars.mem v (free_variables t)


  (** [sentence_p t] checks whether a type contains any (free)
      variables. *)
  let sentence_p t = Vars.is_empty (free_variables t)

  (** Type of a type substitution.  It maps names of type [string] to
      types. *)
  type subst = t IdMap.t


  let find_in_subst v subst =
    try
      IdMap.find v subst
    with
      | Not_found -> Variable v


  (** Apply a substitution [s] to a type. *)
  let rec apply_substitution s =
    function
	Internal -> Internal
      | Basic b -> Basic b
      | Variable x -> find_in_subst x s
      | Application (c, l) ->
	  Application(c, List.map (apply_substitution s) l)
      | Future l ->
	  Future (List.map (apply_substitution s) l)
      | Tuple l ->
	  Tuple (List.map (apply_substitution s) l)
      | Intersection l ->
	  Intersection (List.map (apply_substitution s) l)
      | Disjunction l ->
	  Disjunction (List.map (apply_substitution s) l)
      | Function (d, r) ->
	  Function (apply_substitution s d, apply_substitution s r)


  (** Substitute each occurence of a type variable called [v] by the
      type [t] in the argument type. *)
  let substitute v t = apply_substitution (IdMap.add v t IdMap.empty)


  (** Normalise a substitution.

      A type substitution is said to be in normal form, if
      - The right hand side contains the variable on the left hand
        side, i.e., substituting it would allow substitution of t.
      - The term on the right hand side remains invariant under further
        applications of the substitution.

      The function below tries to compute the normal form of a
      substitution. *)
  let normalise subst =
    (* Try to normalise the binding for [k]. *)
    let rec norm k t =
      let fv = free_variables t in
      let p v = occurs_p v (find_in_subst v subst)
      in
        if (occurs_p k t) || (IdSet.exists p fv) then
	  t
        else
          begin
	    let t' = apply_substitution subst t in
	      if t <> t' then norm k t' else t
          end
    in
      IdMap.mapi norm subst


  (** Make a string of a subtitution *)
  let string_of_substitution subst =
    let f k v a =  (k ^ " |-> " ^ (string_of_type v))::a in
      String.concat ", " (IdMap.fold f subst [])


  (** The type of a method signature. The type [(None,None,None)]
      states that the signature is not known.  The type [(Some t, _,
      _)] states that the method has co-interface t.*)
  type signature = t option * t list option * t list option

  (** Make a default signature. One can supply an optional cointerface
      [coiface]. *)
  let default_sig ?(coiface = None) (): signature =
    (coiface, None, None)

  (** The cointerface of a method with this signature. *)
  let co_interface (c, _, _) = c

  (** The domain type of a method with this signature. *)
  let domain (_, d, _) = d

  (** The range type of a method with this signature. *)
  let range (_, _, r) = r

  (** A string representation of a signature. *)
  let string_of_sig =
    function
      | (None, None, None) ->
	  "[ | -> ]"
      | (Some co, None, None) ->
	  "[ " ^ (string_of_type co) ^ " | unknown -> unknown ]"
      | (None, Some d, None) ->
	  "[ | " ^ (string_of_type_list d) ^ " -> unknown ]"
      | (Some co, Some d, None) ->
	  "[ " ^ (string_of_type co) ^ " | " ^ (string_of_type_list d) ^
	    " -> unknown ]"
      | (None, None, Some r) ->
	  "[ | unknown -> " ^ (string_of_type_list r) ^ " ]"
      | (Some co, None, Some r) ->
	  "[ " ^ (string_of_type co) ^ " | unknown -> " ^
	    (string_of_type_list r) ^ " ]"
      | (None, Some d, Some r) ->
	  "[ | " ^ (string_of_type_list d) ^ " -> " ^
	    (string_of_type_list r) ^ " ]"
      | (Some co, Some d, Some r) ->
	  "[ " ^ (string_of_type co) ^ " | " ^ (string_of_type_list d) ^
	    " -> " ^ (string_of_type_list r) ^ " ]"

end


(** Abstract syntax of expressions. *)
module Expression =
struct

  (** Annotation of the expression. *)
  type note = {
    file: string; (** The file in which the expression occurs. *)
    line: int;	  (** The line in the file in which it occurs. *)
    ty: Type.t    (** The inferred type of the expression. *)
  }

  let make_note ?(file = "**dummy**") ?(line = 0) ?(ty = Type.data) () =
    { file = file ; line = line ; ty = ty }

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
      | Float of note * float
      | String of note * string
      | Id of note * string
      | StaticAttr of note * string * Type.t
      | Tuple of note * t list
      | ListLit of note * t list
      | SetLit of note * t list
      | MapLit of note * (t * t) list
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
      | ObjLit of note * string (* The name of an object. *)
      | LabelLit of note * t list (* The value of the future. *)
  and lhs =
      LhsId of note * string
      | LhsAttr of note * string * Type.t
      | LhsWildcard of note * Type.t option
      | LhsSSAId of note * string * int

  let binaryop_p =
    function
      | "+" | "-" | "*" | "/" | "%" | "**" | "=" | "/=" | "<=" | "<" | ">="
      | ">" | "&&" | "/\\" | "||" | "\\/" | "^" | "=>" | "<=>" | "-|" | "|-"
      | "|-|" | "\\" | "in" ->
	true
      | _ ->
	false

  (* Precedence of binary operators. *)
  let prec_of_binaryop =
    function
      | "**" -> (29, 29)
      | "*" | "/" | "%" -> (31, 31)
      | "+" | "-" -> (33, 33)
      | "\\" -> (35, 35)
      | "<=" | "<" | ">" | ">=" -> (37, 37)
      | "in" -> (41, 41)
      | "|-" | "|-|" | "-|" -> (45, 45)
      | "=" | "/=" -> (51, 51)
      | "&&" | "/\\" -> (55, 55)
      | "^" -> (57, 57)
      | "||" | "\\/" -> (59, 59)
      | "=>" | "<=>" -> (61, 61)
      | o -> assert (not (binaryop_p o)) ; assert false

  let unaryop_p =
    function
      | "~" | "-" | "#" -> true
      | _ -> false

  (* Return the precedence of a unary operator.  Only needed for
     pretty printing. *)
  let prec_of_unaryop =
    function
	"~" -> 53
      | "-" -> 15
      | "#" -> 15
      | _ -> assert false

  (* Extract the annotation of an expression *)
  let note =
    function
      | This a
      | QualifiedThis (a, _)
      | Caller a
      | Now a
      | Null a
      | Nil a
      | History a
      | Bool (a, _)
      | Int (a, _)
      | Float (a, _)
      | String (a, _)
      | Id (a, _)
      | StaticAttr(a, _, _)
      | Tuple (a, _)
      | ListLit (a, _)
      | SetLit (a, _)
      | MapLit (a, _)
      | If (a, _, _, _)
      | FuncCall (a, _, _)
      | Label (a, _)
      | New (a, _, _)
      | Choose (a, _, _, _)
      | Forall (a, _, _, _)
      | Exists (a, _, _, _)
      | Extern (a, _)
      | LabelLit (a, _)
      | ObjLit (a, _)
      | SSAId (a, _, _)
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
      | MapLit (_, l) -> MapLit (note, l)
      | If (_, c, t, f) -> If (note, c, t, f)
      | FuncCall (_, f, a) -> FuncCall (note, f, a)
      | Label (_, l) -> Label (note, l)
      | New (_, c, a) -> New (note, c, a)
      | Choose (_, v, t, p) -> Choose (note, v, t, p)
      | Forall (_, v, t, p) -> Forall (note, v, t, p)
      | Exists (_, v, t, p) -> Exists (note, v, t, p)
      | Extern (_, i) -> Extern (note, i)
      | LabelLit (_, l) -> LabelLit (note, l)
      | ObjLit (_, o) -> ObjLit (note, o)
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
      | MapLit (_, l) ->
          let (dl, rl) = List.split l in
            (List.for_all constant_p dl) && (List.for_all constant_p rl)
      | If (_, c, t, f) -> (constant_p c) && (constant_p t) && (constant_p f)
      | FuncCall (_, _, a) -> List.for_all constant_p a
      | Label _ -> false
      | New _ -> false
      | Choose _ -> false
      | Forall (_, _, _, p) -> constant_p p
      | Exists (_, _, _, p) -> constant_p p
      | Extern _ -> false
      | LabelLit (_, l) -> List.for_all constant_p l
      | ObjLit _ -> true
      | SSAId _ -> false
      | Phi _ -> false

  (* Whether an expression contains a future *)
  let rec contains_future_p =
    function
	Label _ -> true
      | If (_, c, t, f) -> (contains_future_p c) || (contains_future_p t) ||
	  (contains_future_p f)
      | FuncCall(_, _, args) ->
	  List.fold_left (fun a b -> a || (contains_future_p b)) false args
      | New (_, _, args) ->
	  List.fold_left (fun a b -> a || (contains_future_p b)) false args
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
	| MapLit (n, l) ->
	    MapLit (subst_in_note n,
		    List.map (fun (d, r) ->
				(substitute_types_in_expression subst d,
				 substitute_types_in_expression subst r)) l)
	| Id (n, name) ->
	    Id (subst_in_note n, name)
	| StaticAttr (n, name, t) ->
	    StaticAttr (subst_in_note n, name, t)
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
	| LabelLit (n, l) ->
	    LabelLit (subst_in_note n,
		      List.map (substitute_types_in_expression subst) l)
	| ObjLit (n, o) ->
	    ObjLit (subst_in_note n, o)
	| SSAId (n, name, version) ->
	    SSAId (subst_in_note n, name, version)
	| Phi (n, args) ->
	    Phi (subst_in_note n,
		 List.map (substitute_types_in_expression subst) args)

  let rec substitute subst =
    function
      | (This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _
	| History _ | Bool _ | Int _ | Float _ | String _) as e -> e
      | Id (n, v) as e ->
	  begin
	    try
	      set_note n (IdMap.find v subst)
            with
	      | Not_found -> e
          end
      | StaticAttr _ as e -> e
      | Tuple (n, l) ->
	  Tuple (n, List.map (substitute subst) l)
      | ListLit (n, l) ->
	  ListLit (n, List.map (substitute subst) l)
      | SetLit (n, l) ->
	  SetLit (n, List.map (substitute subst) l)
      | MapLit (n, l) ->
          let f (d, r) = (substitute subst d, substitute subst r) in
	    MapLit (n, List.map f l)
      | If (n, c, t, f) ->
	  If (n, substitute subst c, substitute subst t, substitute subst f)
      | FuncCall (n, f, a) ->
	  FuncCall (n, f, List.map (substitute subst) a)
      | Label (n, e) ->
	  Label (n, substitute subst e)
      | New (n, t, a) ->
	  New (n, t, List.map (substitute subst) a)
      | Choose _ ->
	  assert false
      | Forall _ ->
	  assert false
      | Exists _ ->
	  assert false
      | Extern _ as e -> e
      | LabelLit (n, l) ->
	  LabelLit (n, List.map (substitute subst) l)
      | ObjLit _ as e -> e
      | SSAId _ ->
	  assert false
      | Phi _ ->
	  assert false


  (** Negate a boolean expression. *)
  let rec negate_expression =
    function
      | Bool (n, b) -> Bool(n, not b)
      | FuncCall (n, "~", [e]) when Type.bool_p n.ty -> e
      | FuncCall (n, "||", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "&&", [negate_expression e; negate_expression f])
      | FuncCall (n, "&&", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "||", [negate_expression e; negate_expression f])
      | FuncCall (n, "=>", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "&&", [e; negate_expression f])
      | FuncCall (n, "<=>", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "^", [e; f])
      | FuncCall (n, "^", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "<=>", [e; f])
      | FuncCall (n, "=", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "/=", [e; f])
      | FuncCall (n, "/=", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "=", [e; f])
      | FuncCall (n, "<", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "<=", [f; e])
      | FuncCall (n, "<=", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "<", [f; e])
      | FuncCall (n, ">=", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "<", [e; f])
      | FuncCall (n, ">", [e; f]) when Type.bool_p n.ty ->
          FuncCall (n, "<=", [e; f])
      | e -> e


  (** Rewrite a boolean expression to negation normal form (NNF).

      A formula is called in negation normal form, if and only if
      all negation operators are applied to atoms, and the only
      occuring binary connectives are [&&] and [||].  *)
  let rec nnf_of_expression =
    function
      | FuncCall (b, "~", [e]) when Type.bool_p b.ty ->
          nnf_of_expression (negate_expression e)
      | FuncCall (b, ("&&" | "||" as o), [e; f]) when Type.bool_p b.ty ->
	  FuncCall (b, o, [nnf_of_expression e; nnf_of_expression e])
      | FuncCall (b, "=>", [e; f]) when Type.bool_p b.ty ->
	  nnf_of_expression (FuncCall (b, "||", [FuncCall (b, "~", [e]); f]))
      | FuncCall (b, "<=>", [e; f]) when Type.bool_p b.ty ->
	  let e' = FuncCall (b, "=>", [e; f])
	  and f' = FuncCall (b, "=>", [f; e]) in
	    nnf_of_expression (FuncCall (b, "&&", [e'; f']))
      | FuncCall (b, "^", [e; f]) when Type.bool_p b.ty ->
	  nnf_of_expression (FuncCall (b, "~", [FuncCall (b, "<=>", [e; f])]))
      | e -> e


  (** Convert a boolean expression into {i conjunctive normal form}.

      The resulting formula may be exponentially longer.

      Assumes, that the expression is well-typed, that all operators
      have their standard meaning. *)
  let to_cnf f =
    let rec to_cnf_from_nnf =
      function
	| FuncCall (b, "&&", [f; g]) when Type.bool_p b.ty ->
	    FuncCall (b, "&&", [to_cnf_from_nnf f; to_cnf_from_nnf g])
	| FuncCall (b, "||", [f; g]) ->
	    (* Push or inside of and using distributive laws *)
	    let rec to_cnf_or left right =
	      match (left, right) with
		| (FuncCall (lb, "&&", [lf; lg]), _) when Type.bool_p b.ty ->
		    FuncCall (b, "&&", [to_cnf_or lf right; to_cnf_or lg right])
		| (_, FuncCall (rb, "&&", [rf; rg])) when Type.bool_p b.ty ->
		    FuncCall (b, "&&", [to_cnf_or left rf; to_cnf_or left rg])
		| _ ->
		    (* neither subformula contains and *)
		    FuncCall (b, "||", [to_cnf_from_nnf f; to_cnf_from_nnf g])
	    in
	      to_cnf_or f g
	| FuncCall (_, ("=>" | "^" | "<=>"), [_; _]) ->
	    assert false (* Input was assumed to be in NNF *)
	| e -> e
    in
      to_cnf_from_nnf (nnf_of_expression f)

  (* Convert a boolean expression into {i disjunctive normal form}.

     Assumes, that the expression is well-typed, that all operators have
     their standard meaning, and that the expression is not lowered to
     Core Creol. *)
  let to_dnf exp =
    let cnf = to_cnf (nnf_of_expression (negate_expression exp)) in
      nnf_of_expression (negate_expression cnf)

  (* Check whether all occurences of futures are positive in a formula
     f.  Assume, that a future value does not occur as the argument
     of a function call! *)
  let all_futures_positive_p expr =
    let rec all_futures_positive =
      (* Check whether all futures are positive assuming negation normal
	 form *)
      function
	| FuncCall(n, ("&&" | "||"), [left; right]) when Type.bool_p n.ty ->
	    (all_futures_positive left) && (all_futures_positive right)
        | _ -> true
    in
      all_futures_positive (nnf_of_expression expr)
end



(** The abstract syntax of a statement. *)
module Statement =
struct

  open Expression

  (*s Convert a an identifier set to a string. *)

  let string_of_idset s =
    let rec work =
      function
	  [] -> ""
	| [e] -> e
	| e::l -> e ^ ", " ^ (work l)
    in
      "{" ^ (work (IdSet.elements s)) ^ "}"


  (** A definition of the note attached to a statement. *)
  type note = {
    file: string; (** The file in which the expression occurs. *)
    line: int;	  (** The line in the file in which it occurs. *)
    may_def: IdSet.t;    (** The set of local variables that may be defined *)
    must_def: IdSet.t;   (** The set of local variables that must be defined *)
    may_live: IdSet.t;   (** The set of local variables that may live *)
    must_live: IdSet.t;  (** The set of local variables that must live *)
  }


  (** Make a new note for a statement. *)
  let make_note ?(file = "**dummy**") ?(line = 0) () = {
    file = file;
    line = line;
    may_def = IdSet.empty;
    must_def = IdSet.empty;
    may_live = IdSet.empty;
    must_live = IdSet.empty;
  }


  (** {4 Abstract syntax of statements}

      [Skip note] represents a skip statement.

      [Release note] represents an unconditional release statement.

      [Await (note, cond)] represents an await statement for the
      condition [cond].

      [Assert (note, cond)] represents an assert statement for the
      condition [cond].

      [Prove (note, cond)] represents a prove statement for the
      condition [cond].

      [Posit (note, cond)] represents a posit statement for the
      condition [cond].
      
      [Assign (note, lhs, rhs)] represents a multiple assignment
      statement.  Requires that the two lists are of the same
      length.

      [Get (note, future, lhs)] represents a statement that gets the
      result values for [future] and assigns them to [lhs].

      [Free (note, lhs)] deallocates all completion messages for the
      future variables given in [lhs].
      
      [Bury (note, lhs)] represents a special form of assignment,
      setting all its arguments to null.  It does not affect
      life ranges of its arguments and assumes that all argument
      names are already dead at that position.

      [LocalAsyncCall (note, )] The optional [lhs] expression
      represents the value of the name of the variable in which the future
      is stored.  The following argument is the name of the method.  Then
      comes the [signature].  The first optional string is the name of a
      class and denotes the {e upper} bound for searching the method body.
      The next term represents the corresponding {e lower} bound.

      The term {e upper bound} in this context means, that the
      implementation must be defined in a subclass of the given
      class [C], written [<:C].

      The term {e lower bound} in this context means, that the
      implementation must be defined in a superclass of the given
      class [C], written [:>C].
      
  *)

  type t =
    | Skip of note
    | Release of note
    | Await of note * Expression.t
    | Assert of note * Expression.t
    | Prove of note * Expression.t
    | Posit of note * Expression.t
    | Assign of note * Expression.lhs list * Expression.t list
    | Get of note * Expression.t * Expression.lhs list
    | Free of note * Expression.lhs list
    | Bury of note * Expression.lhs list
    | AsyncCall of note * Expression.lhs option * Expression.t * string *
	Type.signature *  Expression.t list
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
    | MultiCast of note * Expression.t * string * Type.signature *
	Expression.t list
    | Tailcall of note * Expression.t * string * Type.signature *
	Expression.t list
    | StaticTail of note * string * Type.signature * string option *
	string option * Expression.t list
    | Return of note * Expression.t list
    | Continue of note * Expression.t
    | If of note * Expression.t * t * t
    | While of note * Expression.t * Expression.t * t
    | DoWhile of note * Expression.t * Expression.t * t
    | Sequence of note * t  * t
    | Merge of note * t * t
    | Choice of note * t * t
    | Extern of note * string


  (** Test, whether the statement is a skip statement. *)
  let skip_p =
    function
	Skip _ -> true
      | _ -> false


  (** Whether a statement is atomic.  This means that the statement cannot
      be lowered. *)
  let rec atomic_p =
    function
      | Skip _
      | Assert _ -> true
      | Prove _ -> false
      | Assign _ | Release _ | Await _ | Posit _ | Get _ | Free _
      | Bury _ -> true
      | AsyncCall (_, None, _, _, _, _) -> false
      | AsyncCall _ -> true
      | SyncCall _ | AwaitSyncCall _
      | LocalAsyncCall (_, None, _, _, _, _, _) -> false
      | LocalAsyncCall _ -> true
      | LocalSyncCall _ | AwaitLocalSyncCall _ -> false
      | MultiCast _ | Tailcall _ | StaticTail _ | Return _ -> true
      | While (_, _, _, s) | DoWhile (_, _, _, s) -> atomic_p s
      | If (_, _, s1, s2) | Sequence (_, s1, s2) | Choice (_, s1, s2) ->
	  (atomic_p s1) && (atomic_p s2)
      | Continue _ -> true
      | Extern _ -> false
      | Merge _ -> assert false


  (** [generate_p stmt] evaluates to [true] if the statement [stmt] is
      contains any statement that is generated by the compiler and which
      cannot occur in source programs. *)
  let rec generated_p =
    function
      | Skip _ | Assert _ | Prove _ | Assign _ | Release _ | Await _ | Posit _
      | Get _ -> false
      | Free _ | Bury _ -> true
      | AsyncCall (_, None, _, _, _, _) -> false
      | AsyncCall (_, Some l, _, _, _, _) -> false
      | SyncCall _ | AwaitSyncCall _
      | LocalAsyncCall (_, None, _, _, _, _, _) -> false
      | LocalAsyncCall (_, Some l, _, _, _, _, _) -> false
      | LocalSyncCall _ | AwaitLocalSyncCall _ | MultiCast _ -> false
      | Tailcall _ | StaticTail _ | Return _ -> true
      | While (_, _, _, s) | DoWhile (_, _, _, s) -> generated_p s
      | If (_, _, s1, s2) | Sequence (_, s1, s2) | Choice (_, s1, s2) ->
	  (generated_p s1) || (generated_p s2)
      | Continue _ -> false
      | Extern _ -> false
      | Merge _ -> assert false


  (** [runtime_p stmt] evaluates to [true] if the statement [stmt] is
      or contains any statement that is generated by the run-time
      system and which cannot occur in source programs and is not
      generated by the compiler. *)
  let rec runtime_p =
    function
      | Skip _ | Assert _ | Prove _ | Assign _ | Release _ | Await _ | Posit _
      | Get _ | Free _ | Bury _ | AsyncCall _ | SyncCall _ | AwaitSyncCall _
      | LocalAsyncCall _ | LocalSyncCall _ | AwaitLocalSyncCall _ | MultiCast _
      | Tailcall _ | StaticTail _ | Return _ -> false
      | While (_, _, _, s) | DoWhile (_, _, _, s) -> generated_p s
      | If (_, _, s1, s2) | Sequence (_, s1, s2) | Choice (_, s1, s2) ->
	  (generated_p s1) || (generated_p s2)
      | Continue _ -> true
      | Extern _ -> false
      | Merge _ -> assert false


  (** Extract the note from a statement. *)
  let note =
    function
      | Skip a | Assert (a, _) | Prove (a, _) | Assign (a, _, _) | Release a
      | Await (a, _) | Posit (a, _) | Get (a, _, _) | Free (a, _)
      | Bury (a, _)
      | AsyncCall (a, _, _, _, _, _)
      | SyncCall (a, _, _, _, _, _)
      | AwaitSyncCall (a, _, _, _, _, _)
      | LocalAsyncCall (a, _, _, _, _, _, _)
      | LocalSyncCall (a, _, _, _, _, _, _)
      | AwaitLocalSyncCall (a, _, _, _, _, _, _)
      | MultiCast (a, _, _, _, _) 
      | Tailcall (a, _, _, _, _) | StaticTail (a, _, _, _, _, _)
      | Return (a, _)
      | If (a, _, _, _) | While (a, _, _, _) | DoWhile (a, _, _, _)
      | Sequence (a, _, _) | Merge (a, _, _) | Choice (a, _, _)
      | Continue (a, _)
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
      | Get (_, l, vs) -> Get (n, l, vs)
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
      | MultiCast (_, c, m, s, i) -> MultiCast (n, c, m, s, i)
      | Tailcall (_, c, m, s, a) -> Tailcall (n, c, m, s, a)
      | StaticTail (_, m, l, u, s, a) -> StaticTail (n, m, l, u, s, a)
      | If (_, c, s1, s2) -> If (n, c, s1, s2)
      | While (_, c, i, s) -> While (n, c, i, s)
      | DoWhile (_, c, i, s) -> DoWhile (n, c, i, s)
      | Sequence (_, s1, s2) -> Sequence (n, s1, s2)
      | Merge (_, s1, s2) -> Merge (n, s1, s2)
      | Choice (_, s1, s2) -> Choice (n, s1, s2)
      | Return (_, el) -> Return (n, el)
      | Continue (_, e) -> Continue (n, e)
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
      | Get (_, _, _) -> "_?(_)"
      | Free (_, _) -> "free _"
      | Bury (_, _) -> "bury _"
      | SyncCall (_, _, _, _, _, _) -> "_._(_;_)"
      | AwaitSyncCall (_, _, _, _, _, _) -> "await _._(_;_)"
      | LocalAsyncCall (_, _, _, _, _, _, _) -> "_!_<:_:>_(_)"
      | LocalSyncCall (_, _, _, _, _, _, _) -> "_<:_:>_(_;_)"
      | AwaitLocalSyncCall (_, _, _, _, _, _, _) -> "await _<:_:>_(_;_)"
      | MultiCast (_, _, _, _, _) -> "!_._(_) as _ *** MultiCast"
      | Tailcall (_, _, _, _, _) -> "tailcall _._(_)"
      | StaticTail (_, _, _, _, _, _) -> "statictail _<:_:>_(_)"
      | If (_, _, _, _) -> "if _ then _ else _ end"
      | While (_, _, _, _) -> "while _ do _ end"
      | DoWhile (_, _, _, _) -> "do _ while _"
      | Sequence (_, _, _) -> "_;_"
      | Merge (_, _, _) -> "_|||_"
      | Choice (_, _, _) -> "_[]_"
      | Continue _ -> "continue _"
      | Return _ -> "return _"
      | Extern (_, s) -> "extern \"" ^ s ^ "\""


  (* Check whether a variable is defined for a statement. *)
  let may_be_defined_p s v =
    IdSet.mem v (note s).may_def


  (* Check whether a variable is life at a statement. *)
  let life_p stmt v = IdSet.mem v (note stmt).may_live


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
        (Release _ | Assert _ | Prove _ | Assign _ | Await _ | Posit _
        | AsyncCall _ | Get _ | Free _ | Bury _ | SyncCall _
        | AwaitSyncCall _ | LocalAsyncCall _ | LocalSyncCall _
        | AwaitLocalSyncCall _ | MultiCast _ | Tailcall _ | StaticTail _
	| Return _ | Continue _ | Extern _) as s -> s
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
      | Merge (note, l, r) ->
	  Merge (note, remove_redundant_skips l, remove_redundant_skips r)
      | Choice (note, l, r) ->
	  Choice (note, remove_redundant_skips l, remove_redundant_skips r)

  let assignment_of_bury =
    function
	Bury (a, (_::_ as l)) ->
	  let nul v =
	    let t = Expression.get_lhs_type v in
	      Expression.Null (Expression.make_note ~ty:t ()) in
	    Assign (a, l, List.map nul l)
      | _ -> assert false


  (** Create a note for an expression from the information provided by
      a statement and type information. *)
  let make_expr_note_from_stmt_note stmt t =
    { Expression.file = stmt.file;
      line = stmt.line;
      ty = t }

end

(** Pragmatic instructions to the compiler.  This module maintains the
    abstract syntax of such a pragmatic instruction and defines their
    types. *)
module Pragma =
struct
  type t = { name: string; values: Expression.t list }

  let pragma_hidden_p { name = n } = n = "Hidden"

  (** Whether the class is hidden. *)
  let hidden_p pragmas = List.exists pragma_hidden_p pragmas

  let hide pragmas =
    if not (hidden_p pragmas) then
      { name = "Hidden"; values = [] }::pragmas
    else
      pragmas

  let show pragmas = List.filter (fun p -> not (pragma_hidden_p p)) pragmas


  let pragma_version_p =
    function
      | { name = "Version"; values = [ _ ] } -> true
      | _ -> false

  let version pragmas =
    try
      match List.find pragma_version_p pragmas with
        | { values = [ Expression.Int (_, v) ] } -> v
        | _ -> assert false
    with
      | Not_found -> Big_int.zero_big_int

  let increase_version pragmas =
    let v = version pragmas in
    let v' = Expression.Int (Expression.make_note (), Big_int.succ_big_int v) in
      { name = "Version"; values = [ v' ] } ::
        (List.filter (fun e -> not (pragma_version_p e)) pragmas)

end


(** Abstract syntax of variable declarations. *)
module VarDecl =
struct
  type t =
    { name: string;
      var_type: Type.t;
      init: Expression.t option;
      file: string;
      line: int;
    }
end


(** Abstract syntax of method declarations and definitions *)
module Method =
  struct

  (** Abstract syntax tree node of a method declaration or method definition.
      If [body] is [None], then the node represents a declaration.  If it
      is not [None], the node represents a method definition.

      The member [location] indicates the class or interface in which this
      method declaration or definition is defined.  
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
	location: string;
        file: string;
        line: int
      }

    (* This is the empty method.  It is used by the type checker
       for checking types on class level expressions. *)

    let empty =
      { name = ""; coiface = Type.Internal; inpars = []; outpars = [];
	requires = Expression.Bool(Expression.make_note (), true);
	ensures = Expression.Bool(Expression.make_note (), true);
	vars = []; body = None; location = ""; file = ""; line = 0 }

    let compare m n =
      let r1 = String.compare m.name n.name in
      let r2 = match (m.coiface, n.coiface) with
	| (Type.Internal, Type.Internal) -> 0
	| (Type.Internal, _) -> -1
	| (_, Type.Internal) -> 1
	| (s, t) -> String.compare (Type.name s) (Type.name t)
      in
      let rec c =
	function
	  | ([], []) -> 0
	  | ([], _) -> -1
	  | (_, []) -> 1
	  | ({ VarDecl.var_type = a }::r, { VarDecl.var_type = b }::t) ->
	      String.compare (Type.name a) (Type.name b)
      in
      let r3 = c (m.inpars, n.inpars) in
      let r4 = c (m.outpars, n.outpars) in
	match () with
	  | () when r1 <> 0 -> r1
	  | () when r2 <> 0 -> r2
	  | () when r3 <> 0 -> r3
	  | () when r4 <> 0 -> r4
          | () -> 0

    let make_decl n inp outp r e file line =
      { name = n; coiface = Type.Internal; inpars = inp; outpars = outp;
	requires = r; ensures = e; vars = []; body = None; location = "";
        file = file; line = line }

    let set_cointerface cf m = { m with coiface = cf }


    (* Internal helper function to build a type signature from a list
       [l] of variable declarations. *)

    let build_type l =
      Type.Tuple (List.map (fun v -> v.VarDecl.var_type) l)

    let domain_type m = build_type m.inpars

    let range_type m = build_type m.outpars

    (* Build a method signature type from the declaration. *)
    let signature m: Type.signature =
      (Some m.coiface,
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


    (* Determine whether a local variable is a future. *)
    let future_p ~meth name =
      Type.future_p (find_variable meth name).VarDecl.var_type


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





(** Abstract syntax of a with clause.

    A with clause consists of a co-interface name, a list of methods
    and a sequence of invariants. *)
module With = struct

  type t = {
    co_interface: Type.t;
    methods: Method.t list;
    invariants: Expression.t list;
    file: string;
    line: int
  }

end



(** Abstract syntax of inherits, implements, and contracts declarations *)
module Inherits =
struct
  type t = {
    name: string;
    arguments: Expression.t list;
    file: string;
    line: int
  }

  let name { name = n } = n

  let arguments { arguments = a } = a
end



(** Abstract syntax of classes. *)
module Class =
struct

  type t =
      { name: string;
	parameters: VarDecl.t list;
	inherits: Inherits.t list;
	contracts: Inherits.t list;
	implements: Inherits.t list;
	attributes: VarDecl.t list;
	invariants: Expression.t list;
	with_defs: With.t list;
	objects_created: Big_int.big_int;
	pragmas: Pragma.t list;
	file: string;
	line: int;
      }

  let empty =
    { name = ""; parameters = []; inherits = []; contracts = [];
      implements = []; attributes = []; invariants = []; with_defs = [];
      objects_created = Big_int.zero_big_int; pragmas = [];
      file = ""; line = 0 }

  (** Whether the class is hidden. *)
  let hidden_p c = Pragma.hidden_p c.pragmas

  (** Hide a class. *)
  let hide c = { c with pragmas = Pragma.hide c.pragmas }

  (** Show a class. *)
  let show c = { c with pragmas = Pragma.show c.pragmas }

  (** Get the version of a class. *)
  let version c = Pragma.version c.pragmas

  (** Increase the version of a class [c] *)
  let increase_version c =
    { c with pragmas = Pragma.increase_version c.pragmas }


  (** Get the interface type implemented by a class.  If it does not
      declare interfaces, then the result is [Any].  Filters
      out duplicates. *)
  let get_type cls =
    let ordered =
      List.fast_sort String.compare
	(List.fold_left (fun a { Inherits.name = t } -> if  List.mem t a then a else t::a)
	   [] (cls.implements @ cls.contracts))
    in
      match ordered  with
	| [] -> Type.any
	| [t] -> Type.Basic t
	| ts -> Type.Intersection (List.map (fun t -> Type.Basic t) ts) 

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

  (** Add a new method definition to a class. Assumes that there is no
      other method definition with the same name and signature. *)
  let add_method_to_class cls mtd =
    { cls with with_defs =
               { With.co_interface = mtd.Method.coiface;
                 invariants = [];
                 methods = [mtd];
                 file = ""; line = 0 }::cls.with_defs; }
                 

end




(** Abstract syntax of interfaces *)
module Interface =
struct

  type  t =
      { name: string;
	parameters: VarDecl.t list;
	inherits: Inherits.t list;
	with_decls: With.t list;
        pragmas: Pragma.t list;
        file: string;
        line: int;
      }

  let empty = { name = ""; parameters = []; inherits = []; with_decls = [];
                pragmas = []; file = ""; line = 0 }

  (** Whether the interface is hidden. *)
  let hidden_p i = Pragma.hidden_p i.pragmas

  (** Hide a interface. *)
  let hide i = { i with pragmas = Pragma.hide i.pragmas }

  (** Show a interface. *)
  let show i = { i with pragmas = Pragma.show i.pragmas }

  let compare { name = m } { name = n } = String.compare m n

end





(** Abstract syntax of interfaces. *)
module Exception =
struct
  type t = { name: string; parameters: VarDecl.t list; pragmas: Pragma.t list }

  (** Whether the exception is hidden. *)
  let hidden_p e = Pragma.hidden_p e.pragmas

  (** Hide a exception. *)
  let hide e = { e with pragmas = Pragma.hide e.pragmas }

  (** Show a exception. *)
  let show e = { e with pragmas = Pragma.show e.pragmas }
end





(** Abstract syntax of function definitions. *)
module Function =
struct

  type t = {
    name: string;
    parameters: VarDecl.t list;
    result_type: Type.t;
    body: Expression.t;
    pragmas: Pragma.t list }

  let domain_type f =
    Type.Tuple (List.map (fun v -> v.VarDecl.var_type) f.parameters)

  let range_type f = f.result_type

  let signature f = Type.Function(domain_type f, range_type f)


  (** Whether the function is hidden. *)
  let hidden_p f = Pragma.hidden_p f.pragmas

  (** Hide a function. *)
  let hide f = { f with pragmas = Pragma.hide f.pragmas }

  (** Show a function. *)
  let show f = { f with pragmas = Pragma.show f.pragmas }

  (* If a function has an external definition, then this function
     returns its value.  Otherwise, raise [Not_found]. *)

  let external_definition { body = b } =
    match b with
      | Expression.Extern (_, s) -> s
      | _ -> raise Not_found     

end



(** Abstract syntax of data type declarations. *)
module Datatype =
struct

  type t = {
    name: Type.t;
    supers: Type.t list;
    pragmas: Pragma.t list;
      (* Hide from output.  Set for datatypes defined in the prelude. *)
    file: string;
    line: int;
  }

  (** Whether the class is hidden. *)
  let hidden_p c = Pragma.hidden_p c.pragmas

  (** Hide a class. *)
  let hide c = { c with pragmas = Pragma.hide c.pragmas }

  (** Show a class. *)
  let show c = { c with pragmas = Pragma.show c.pragmas }

end


(** Abstract syntax of processes. *)
module Process =
struct

  type t = {
    attributes: VarDecl.t list;
    code: Statement.t
  }

end


(** Abstract syntax of objects. *)
module Object =
struct

  type t = {
    name: Expression.t;
    cls: Type.t;
    attributes: VarDecl.t list;
    process: Process.t;
    process_queue: Process.t list;
    emitted_calls: Big_int.big_int;
    pragmas: Pragma.t list;
  }

  (** Whether the class is hidden. *)
  let hidden_p c = Pragma.hidden_p c.pragmas

  (** Hide a class. *)
  let hide c = { c with pragmas = Pragma.hide c.pragmas }

  (** Show a class. *)
  let show c = { c with pragmas = Pragma.show c.pragmas }

end


(** Abstract syntax of a future object. *)
module Future =
struct

  type t = {
    name: Expression.t;
    completed: bool;
    references: Big_int.big_int;
    value: Expression.t list;
  }

end


(** {2 Dynamic Reconfiguration}

  The following modules are concerned with the abstract syntax of dynamic
  updates *)

(** {3 Dependencies}

    Version dependencies of classes and objects.

    Requires that objects can be uniquely identified by a string. *)
module Dependency =
struct

  type t = {
    name: string;
    version: Big_int.big_int;
  }

  let compare d e =
    let r1 = compare d.name e.name in
      if r1 <> 0 then
        r1
      else
        Big_int.compare_big_int d.version e.version

end


(** {3 Dependencies}

    A set of dependencies. *)
module Dependencies = Set.Make(Dependency)



(** {3 New Class}

    New class update term *)
module NewClass =
struct

  type t = {
    cls: Class.t;
    dependencies: Dependencies.t;
  }

end



(** {3 Class Upgrade}

    The abstract syntax of a class upgrade term. *)
module Update =
struct

  type t = {
    name: string; (** The name of the class to upgrade. *)
    inherits: Inherits.t list;
    contracts: Inherits.t list;
    implements: Inherits.t list;
    attributes: VarDecl.t list;
    with_defs: With.t list;
    pragmas: Pragma.t list;
    dependencies: Dependencies.t
  }

  let apply u c =
    assert (u.name = c.Class.name) ;
    { c with Class.inherits = c.Class.inherits @ u.inherits ;
      contracts = c.Class.contracts @ u.contracts ;
      implements = c.Class.implements @ u.implements ;
      attributes = c.Class.attributes @ u.attributes ;
      with_defs = c.Class.with_defs @ u.with_defs (** XXX this needs to change. *)
    }

end


(** {3 Retract Features From Class} *)
module Retract =
struct

  type t = {
    name: string; (** The name of the class to simplify. *)
    inherits: Inherits.t list;
    attributes: VarDecl.t list;
    with_defs: With.t list;
    pragmas: Pragma.t list;
    dependencies: Dependencies.t;
    obj_deps: Dependencies.t;
  }

end


(** Abstract syntax of Declararions. *)
module Declaration =
struct

  type t =
      | Class of Class.t
      | Interface of Interface.t
      | Datatype of Datatype.t
      | Exception of Exception.t
      | Function of Function.t
      | Object of Object.t
      | Future of Future.t
      | NewClass of NewClass.t
      | Update of Update.t
      | Retract of Retract.t


  let hide =
    function
      | Class c -> Class (Class.hide c)
      | Interface i -> Interface (Interface.hide i)
      | Datatype d -> Datatype (Datatype.hide d)
      | Exception e -> Exception (Exception.hide e)
      | Function f -> Function (Function.hide f)
      | Object o -> Object (Object.hide o)
      | Future f -> Future f
      | NewClass u -> NewClass u
      | Update u -> Update u
      | Retract u -> Retract u


  let show =
    function
      | Class c -> Class (Class.show c)
      | Interface i -> Interface (Interface.show i)
      | Datatype d -> Datatype (Datatype.show d)
      | Exception e -> Exception (Exception.show e)
      | Function f -> Function (Function.show f)
      | Object o -> Object (Object.show o)
      | Future f -> Future f
      | NewClass u -> NewClass u
      | Update u -> Update u
      | Retract u -> Retract u

end


(** Abstract syntax of a program.

    A program is is currently just a list of its declarations. This
    actual type may change in a future version. Do not use List
    functions directly, but use the functions defined in this module
    only.  *)
module Program =
struct

  (** The type of a program. *)
  type t = { decls: Declaration.t list }


  (** Make a [Program.t] from a list [l] of declarations. *)
  let make decls = { decls = decls }

  (** Concatenate programs. *)
  let concat programs =
    { decls = List.concat (List.map (fun p -> p.decls) programs) }


  (** Compute the transitive closure of a relation. *)
  let transitive_closure rel =
    let rec do_it r =
      let f s = IdSet.fold (fun elt acc -> IdSet.union (IdMap.find elt r) acc) s s in
      let r' = IdMap.fold (fun key elt acc -> IdMap.add key (f elt) acc) r r in
	if IdMap.equal IdSet.equal r r' then
	  r
	else
	  do_it r'
    in
      do_it rel


  (** {4 Classes}

      The following functions are concerned with class definitions.
      The abstract syntax of classes is defined in {! Creol.Class}. *)

  (** Raise [Class_not_found file line name] if the class [name] is
      not found in file [file] and line [line]. *)
  exception Class_not_found of string * int * string

  (** [find_class program name] attempts to find a class called [name]
      in [program].  It raise a [Not_found] exception if no class has
      the name [name] in [program]. *)
  let find_class program name =
    let class_with_name =
      function
	| Declaration.Class { Class.name = n } -> n = name
	| _ -> false
    in
      match List.find class_with_name program.decls with
	| Declaration.Class cls -> cls
	| _ -> assert false

  let remove_class program name =
    let not_class_with_name =
      function
	| Declaration.Class { Class.name = n } -> n <> name
	| _ -> true
    in
      { decls = List.filter not_class_with_name program.decls }


  let add_class program cls =
    { decls = (Declaration.Class cls)::program.decls }


  let replace_class program cls =
    add_class (remove_class program cls.Class.name) cls
    


  (** [type_of_class program name] returns the type of the class
      called [name] in [program].  It raise a [Not_found] exception if
      no class has the name [name] in [program]. *)
  let type_of_class program name =
    Class.get_type (find_class program name)


  (** Compute the class hierarchy of a program. *)
  let class_hierarchy program =
    let add_class a { Inherits.name = n; file = f; line = l } =
      try
        ignore (find_class program n) ; IdSet.add n a
      with
        | Not_found -> raise (Class_not_found (f, l, n))
    in
    let f rel =
      function
	| Declaration.Class { Class.name = name; inherits = inh } ->
	    IdMap.add name (List.fold_left add_class IdSet.empty inh) rel
	| _ -> rel
    in
      List.fold_left f IdMap.empty program.decls


  (** [superclasses program name] returns the set of all super-classes
      of a class [name] in [program].  Raises a [Class_not_found]
      exception in the context of the class from which the class is
      supposed to be inherited. A [Not_found] exception is raised if a
      class called [name] does not exist in [program]. *)
  let superclasses program name =
    let rec work s a { Inherits.name = cls } =
      let a' =
	let c =
	  try
	    find_class program cls
	  with
	      Not_found ->
		raise (Class_not_found (s.Class.file , s.Class.line, cls))
	in
	  List.fold_left (work c) a c.Class.inherits
      in
	IdSet.add cls a'
    in
    let c = find_class program name in
      List.fold_left (work c) IdSet.empty c.Class.inherits


  (** [diamonds program name] is the set of all classes in [program]
      that the class called [name] inherits from more than one of its
      super-classes. It raises a [Not_found] exception if [name] (or
      one of its direct super classes, but this is a bug) does not
      exist in [program] and a [Class_not_found] exception if one of
      the super-classes does not exist in [program].  *)
  let diamonds program name =
    let supers =
      (* A list of sets of classes inherited by each direct super class of
         [name]. *)
      let f { Inherits.name = c } = IdSet.add c (superclasses program c) in
        List.map f (find_class program name).Class.inherits
    in
    let common this =
      let others =
        let f a e = if e == this then a else IdSet.union a e in
          List.fold_left f IdSet.empty supers
      in
        IdSet.inter this others
    in
      List.fold_left (fun a e -> IdSet.union (common e) a) IdSet.empty supers


  (** Return true if [s] is a subclass of [t]. *)
  let subclass_p program s t =
    let rec search s =
      (s = t) ||
	try
	  let s' = find_class program s in
	    (List.exists (fun u -> search u) (List.map Inherits.name s'.Class.inherits))
	with
	    Not_found -> false
    in search s


  (** Returns the set of names of all subclasses of a class called [c]. *)
  let subclasses program c =
    let f a =
      function
        | Declaration.Class { Class.name = n } when subclass_p program n c ->
            IdSet.add n a
        | _ -> a
     in
       List.fold_left f IdSet.empty program.decls


  (** {4 Interfaces}

      The following functions are concerned with interfaces.  *)

  (** Raise [Interface_not_found file line name] if the interface [name]
      is not found in file [file] and line [line]. *)
  exception Interface_not_found of string * int * string


  (** [find_interface program name] returns the interface definition of the
      interface called [name] in [program].  It raises [Not_found] if
      no interface called [name] is defined in [program].  *)
  let find_interface program name =
    let interface_with_name =
      function
	| Declaration.Interface { Interface.name = n } -> name = n
	| _ -> false
    in
      match List.find interface_with_name program.decls with
	| Declaration.Interface i -> i
	| _ -> assert false


  (** [interface_p program iface] is true, if the type [iface] refers to
      interface in [program] *)
  let interface_p program iface =
    match iface with
	Type.Internal -> true
      | Type.Basic n ->
	  let p =
	    function
	      | Declaration.Interface { Interface.name = n' } -> n = n'
	      | _ -> false
	  in
	    List.exists p program.decls
      | _ -> false


  (** [subinterface_p program s t] returns true if [s] is a subinterface of
      [t] in [program]. *)
  let subinterface_p program s t =
    if t = "Any" then (* Everything is a sub-interface of [Any]. *)
      true
    else
      let rec search s =
	(s = t) ||
	  try
	    let s' = find_interface program s in
	      (List.exists (fun u -> search u)
		 (List.map Inherits.name s'.Interface.inherits))
	  with
	      Not_found -> false
      in
	search s


  (** Return true if the class [cls] contracts the interface [iface]. *)
  let contracts_p program cls iface =
    let p i = subinterface_p program i (Type.string_of_type iface) in
      (Type.any_p iface) || (List.exists p (List.map Inherits.name cls.Class.contracts))


  (** [class_provides prg cls] collects the set of all interfaces
      implemented by the class [cls] in program [prg].  These are the
      interfaces contracted by all superclasses, the interfaces
      immediately implemented and the interface [Any].

      The result is a set of interface names. *)
  let class_provides ~program ~cls =
    let findc n =
      try
	find_class program n
      with 
	  Not_found ->
	    raise (Class_not_found (cls.Class.file, cls.Class.line, n))
    and findi n =
      try
	find_interface program n
      with 
	  Not_found ->
	    raise (Interface_not_found (cls.Class.file, cls.Class.line, n))
    in
    let rec work_class a c =
      (* Recursively collect all interfaces contracted by the class
	 [c]. *)
      let a' = List.fold_left
        (fun a { Inherits.name = n } -> work_iface a (findi n)) a c.Class.contracts
      in
	List.fold_left
          (fun a { Inherits.name = n } -> work_class a (findc n)) a' c.Class.inherits
    and work_iface a i =
      (* Recursively collect all interfaces inherited by the interface
	 [i]. *)
      let a' = List.fold_left 
        (fun a { Inherits.name = n } -> work_iface a (findi n)) a i.Interface.inherits
      in
        IdSet.add i.Interface.name a'
    in
    let ic =
      List.fold_left (fun a { Inherits.name = n } -> work_iface a (findi n))
	IdSet.empty cls.Class.implements
    in
      IdSet.add "Any" (work_class ic cls)


  (** {4 Data types}

      Functions relating to data types. *)

  (** Raise [Datatype_not_found file line name] if the datatype [name]
      is not found in file [file] and line [line]. *)
  exception Datatype_not_found of string * int * string


  (** Find the definition of the data type called [name] in [program]. *)
  let find_datatype ~program ~name =
    let datatype_with_name =
      function
	| Declaration.Datatype { Datatype.name = Type.Basic n }
	    when n = name -> true
	| Declaration.Datatype { Datatype.name = Type.Application (n, _) }
	    when n = name -> true
	| _ -> false
    in
      match List.find datatype_with_name program.decls with
	| Declaration.Datatype d -> d
	| _ -> assert false


  (** Return true if [s] is a sub-datatype of [t] *)
  let rec sub_datatype_p program s t =
    try
      let s_decl =
	find_datatype program s
      in
	(s = t) ||
	  (List.exists (function u -> sub_datatype_p program u t)
	     (List.map Type.string_of_type s_decl.Datatype.supers))
    with
	Not_found -> false


  (** {4 Types}

      Functions for types. *)

  (** Check, whether [ty] is a type in [program]. *)
  let type_p ~program ~ty =
    let p name' =
      function
        | Declaration.Interface { Interface.name = n } -> (name' = n)
        | Declaration.Datatype { Datatype.name = t } -> (name' = (Type.name t))
	| _ -> false
    in
    let rec work_p =
      function 
	| Type.Internal ->
	    true
	| Type.Basic n ->
	    List.exists (p n) program.decls
	| Type.Variable _ ->
	    true
	| Type.Application (n, a) ->
	    (List.exists (p n) program.decls) && (List.for_all work_p a)
	| Type.Future l ->
	    List.for_all work_p l
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


  (** Find all definitions of functions called [name] in [program],
      whose formal parameters are compatible with [domain].  Only
      return the most specific matches.  Returns the empty list if none
      is found. *)
  let find_functions program name =
    let p a =
      function
	| Declaration.Function f when f.Function.name  = name -> f::a
	| _ -> a
    in
      List.fold_left p [] program.decls


  (** Find the class declaration for an attribute. [cls] is the class
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
	    match work (find_class program (Inherits.name i)) with
		None -> search r
	      | cls' -> cls'
    in
      match work cls with
	  None -> raise Not_found
	| Some cls' -> cls'

  let find_attr_decl ~program ~cls ~name =
    let c = find_class_of_attr program cls name in
      Class.find_attr_decl c name


  (** Compute the interface of a class, i.e., the set of all method it
      implements. We call this interface the {e full descriptor.} *)
  let full_class_descriptor ~program ~cls = assert false


  (** Decides whether [s] is a subtype of [t] in [program]. *)
  let subtype_p program s t =
    let rec work =
      function 
	| (_, _) when s = t -> true
	| (_, Type.Variable _) -> true
	| (_, Type.Basic "Data") when Type.sentence_p s -> true 
	| (Type.Basic st, Type.Basic tt) ->
	    (sub_datatype_p program st tt) || (subinterface_p program st tt)
	| (_, Type.Intersection l) ->
	    List.for_all (fun u -> work (s, u)) l
	| (_, Type.Disjunction l) ->
	    List.exists (fun u -> work (s, u)) l
	| (Type.Application (sc, sa), Type.Application (tc, ta)) ->
	    (sc = tc) &&
	      begin
		try 
		  List.for_all2 (fun u v -> work (u, v)) sa ta
		with
		    Invalid_argument _ -> false
	      end
	| (Type.Application _, _) -> false
	| (Type.Future sa, Type.Future ta) ->
	      begin
		try 
		  List.for_all2 (fun u v -> work (u, v)) sa ta
		with
		    Invalid_argument _ -> false
	      end
	| (Type.Future sa, _) -> false
	| (Type.Tuple sa, Type.Tuple ta) ->
	    begin
	      try 
		(List.for_all2 (fun u v -> work (u, v)) sa ta)
	      with
		  Invalid_argument _ -> false
	    end
	| (Type.Tuple _, _) -> false
	| (Type.Intersection sa, _) ->
	    List.exists (fun s -> work (s, t)) sa
	| (Type.Disjunction sa, _) ->
	    List.for_all (fun s -> work (s, t)) sa
	| ((Type.Internal, _) | (_, Type.Internal)) -> false
	| (Type.Function (d1, r1), Type.Function (d2, r2)) -> 
	    (work (d1, d2)) && (work (r2, r1))
	| (Type.Variable _, _) -> true
	| (Type.Function _, _) -> false
	| (Type.Basic _, _) -> false
    in
      work (s, t)


  (** Return the greates lower bound of all types in [lst] in
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


  (** Return the least upper bound of all types in [lst] in [program],
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



  (** Return a string representation of a cycle. *)
  let string_of_cycle c = String.concat " <: " c



  let cycle rel =
    let f k e a = if IdSet.mem k e then IdSet.add k a else a in
      IdMap.fold f rel IdSet.empty


  (** Test whether the type relation is acyclic. *)
  let acyclic_p rel = IdSet.is_empty (cycle rel)


  (** Find a cycle.  This is using depth first search. *)
  let find_cycle rel =
    let rec build (res: string list) (current: string) =
	search (current::res) (IdMap.find current rel)
    and search (res: string list) supers =
      if IdSet.is_empty supers then
	res
      else
	begin
	  let cand: string = IdSet.choose supers in
	    if List.mem cand res then
	      cand::res
	    else
	      begin
	        let res' = build res cand in
	          if List.mem cand res' then
		    res'
		  else
		    search res (IdSet.remove cand supers)
	      end
	end
    in
      build [] (IdSet.choose (cycle (transitive_closure rel)))


  (** Compute the subtype relation-ship of the program. *)
  let subtype_relation program =
    let add_iface a { Inherits.name = i; file = f; line = l } =
      try 
        ignore (find_interface program i); IdSet.add i a
      with
        | Not_found -> raise (Interface_not_found (f, l, i))
    and add_datatype f l a d =
      try
        ignore (find_datatype program (Type.name d)); IdSet.add (Type.name d) a
      with
        Not_found -> raise (Datatype_not_found (f, l, Type.string_of_type d))
    in
    let f rel =
      function
	| Declaration.Interface { Interface.name = name; inherits = supers } ->
	    IdMap.add name (List.fold_left add_iface IdSet.empty supers) rel
	| Declaration.Datatype { Datatype.name = name; supers = supers; file = file; line = line } ->
	    IdMap.add (Type.name name)
	      (List.fold_left (add_datatype file line) IdSet.empty supers) rel
	| _ -> rel
    in
      List.fold_left f IdMap.empty program.decls


  (** {4 Functions} *)

  (** Find the definition of a function [name] in [program] that has
      signature [sig].  The result should be unique. *)
  let find_function ~program ~name ~sg =
    let p f = subtype_p program sg (Function.signature f)
    and q s t =
      if (subtype_p program (Function.signature s) (Function.signature t)) then
        s
      else
        t
    in
    let l = List.find_all p (find_functions program name) in
      try
        List.fold_left q (List.hd l) (List.tl l)
      with
        | Failure("tl") ->
	    raise (Failure ("No candidate for " ^ name ^ ": " ^
		    (Type.string_of_type sg)))


  (** {4 Methods} *)

  let find_method_in_with program name signature w =
    let (_, ins, outs) = signature in
    let rng = match outs with None -> Type.data | Some t -> Type.Tuple t in
    let p m =
      m.Method.name = name &&
      (match ins with
	   None -> true
	 | Some t -> subtype_p program (Type.Tuple t) (Method.domain_type m)) &&
      (subtype_p program (Method.range_type m) rng)
    in
      List.filter p w.With.methods


  (** Find all definitions of a method called [name] that matches the
      signature [(coiface, ins, outs)] in [iface] and its
      super-interfaces.  *)
  let interface_find_methods ~program ~iface ~name (coiface, ins, outs) =
    let asco = match coiface with None -> Type.any | Some c -> c in
    let rec find_methods_in_interface i =
      let q w = subtype_p program asco w.With.co_interface in
      let withs = List.filter q i.Interface.with_decls in
      let here =
	List.fold_left
	  (fun a w ->
	     (find_method_in_with program name (coiface, ins, outs) w)@a)
	  [] withs
      and supers = List.map Inherits.name i.Interface.inherits
      in
	List.fold_left
          (fun r i ->
             (find_methods_in_interface (find_interface program i))@r)
          here supers
    in
      find_methods_in_interface iface


  (** Check whether the interface [iface] or one of its
      superinterfaces provide a method matching the [signature]. *)
  let interface_provides_p ~program ~iface ~meth signature =
    [] <> (interface_find_methods program iface meth signature)


  (** Find all definitions of a method called [name] that matches the
      signature [(coiface, ins, outs)] in class [cls] and its
      super-classes.

      Used by the type checker to find all suitable method definitions
      or method declarations. *)
  let find_methods_in_class ~program ~cls ~name (coiface, ins, outs) =
    let asco = match coiface with None -> Type.any | Some c -> c in
    let rec find c =
      let q w = subtype_p program asco w.With.co_interface in
      let withs = List.filter q c.Class.with_defs in
      let here =
	List.fold_left
	  (fun a w ->
	     (find_method_in_with program name (coiface, ins, outs) w)@a)
	  [] withs
      and supers = List.map Inherits.name c.Class.inherits
      in
	List.fold_left
          (fun r i -> (find (find_class program i))@r)
          here supers
    in
      find cls


  (** Find the first class in [cls] or below that defines a method called
      [meth] with signature [(coiface, ins, outs)].  *)
  let find_class_of_method program cls name (coiface, ins, outs) =
    let co = match coiface with None -> Type.any | Some c -> c in
    let q w = subtype_p program co w.With.co_interface in
    let rec find =
      function
        | [] ->
            raise Not_found
        | c::l ->
           let cls' = find_class program c in
           let withs = List.filter q cls'.Class.with_defs in
           let methods =
             List.concat
               (List.map (find_method_in_with program name (coiface, ins, outs))
               withs)
            in
             begin
               match methods with
                 | [] ->
                    let supers = List.map Inherits.name cls'.Class.inherits in
                      begin
                        try
                          find supers
                        with
                          | Not_found -> find l
                      end
                 | _ -> c
             end
    in
      find_class program (find [cls.Class.name])


  (** Check whether the class [cls] or one of its superclasses provide
      a method called [meth] matching the [signature]. *)
  let class_provides_method_p ~program ~cls meth signature =
    [] <> (find_methods_in_class program cls meth signature)


  (** Remove a method from a class.

      This function is used to replace all methods in a class by its
      updated method. *)
  let remove_method_from_class program cls mtd =
    let m_p m = not ((m.Method.name = mtd.Method.name) &&
      (subtype_p program m.Method.coiface mtd.Method.coiface) &&
        (subtype_p program (Method.domain_type m) (Method.domain_type mtd)) &&
          (subtype_p program (Method.range_type mtd) (Method.range_type m)))
    in
    let mf w = { w with With.methods = List.filter m_p w.With.methods } in
    let m' = List.map mf cls.Class.with_defs in
    let w' = List.filter (fun w -> [] <> w.With.methods) m'
    in
      { cls with Class.with_defs = w' }


  (** {4 Iterators} *)

  let iter program f = List.iter f program.decls

  let map program f = { decls = List.map f program.decls }

  (** Apply a function to each method defined in the program. *)
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
	| Declaration.Class c -> Declaration.Class (for_class c)
	| Declaration.Interface _ -> d
	| Declaration.Exception _ -> d
	| Declaration.Datatype _ -> d
	| Declaration.Function _ -> d
	| Declaration.Object _ -> d
        | Declaration.Future _ -> d
        | Declaration.NewClass _ -> d
        | Declaration.Update _ -> d
        | Declaration.Retract _ -> d
    in
      { decls = List.map for_decl program.decls }


  (** {4 Declarations} *)

  (** Hide all declarations. *)
  let hide_all program =
    map program Declaration.hide


  (** Show all objects and hide all other elements. *)
  let show_only_objects prg =
    let f = function 
      | Declaration.Object _ as d -> Declaration.show d
      | d -> Declaration.hide d
    in
      map prg f


  (** Hide all objects in [prg]. Other declarations keep their
      status. *)
  let hide_all_objects prg =
    let f = function 
      | Declaration.Object _ as d -> Declaration.hide d
      | d -> d
    in
      map prg f


  (** {4 Dynamic Updates} *)

  (** Apply an update to a class. *)
  let apply_update_to_class program cls upd =
    let inherits' = cls.Class.inherits @ upd.Update.inherits
    and contracts' = cls.Class.contracts @ upd.Update.contracts
    and implements' = cls.Class.implements @ upd.Update.implements
    and attrs' = cls.Class.attributes @ upd.Update.attributes
    in
    let cls' = { cls with Class.inherits = inherits';
                          contracts = contracts';
			  implements = implements';
			  attributes = attrs' }
    in
    let cls'' =
      let with_with c w =
        List.fold_left (remove_method_from_class program) c w.With.methods
      in
        List.fold_left with_with cls' upd.Update.with_defs
    in
      let with_with c w =
        List.fold_left (Class.add_method_to_class) c w.With.methods
      in
        List.fold_left with_with cls'' upd.Update.with_defs


  let apply_retract_to_class program cls upd =
    let inherits' =
      let f a e =
        List.filter (fun e' -> e.Inherits.name <> e'.Inherits.name) a
      in
        List.fold_left f cls.Class.inherits upd.Retract.inherits
    and attributes' =
      let f a e =
        List.filter (fun e' -> e.VarDecl.name <> e'.VarDecl.name) a
      in
        List.fold_left f cls.Class.attributes upd.Retract.attributes
    and with_defs' =
      let f a e =
        List.map
          (fun e' -> if (e.With.co_interface = e'.With.co_interface) then
                       begin
                         let g a m =
                           List.filter (fun m' -> (m.Method.name <> m'.Method.name) && (m.Method.inpars <> m'.Method.inpars) && (m.Method.outpars <> m'.Method.outpars)) a
                         in
                           { e with With.methods = List.fold_left g e.With.methods e'.With.methods }
                       end
                     else
                       e) a
      in
        List.fold_left f cls.Class.with_defs upd.Retract.with_defs
    in
      Class.increase_version { cls with Class.inherits = inherits';
                                        attributes = attributes';
                                        with_defs = with_defs' }


  (** Apply all updates in [updates] to [program] *)
  let apply_updates program updates =
    let f prg =
      function
        | Declaration.NewClass upd ->
            begin
              try
                ignore (find_class prg upd.NewClass.cls.Class.name) ;
                raise (Failure "Class exists")
              with
                Not_found ->
                  let cls = Class.increase_version upd.NewClass.cls in
                    add_class program cls
            end
        | Declaration.Update ({ Update.name = name } as upd) ->
            let cls = find_class prg name in
            let cls' = apply_update_to_class prg cls upd in
              replace_class prg cls'
        | Declaration.Retract ({ Retract.name = name } as upd) ->
            let cls = find_class prg name in
            let cls' = apply_retract_to_class prg cls upd in
              replace_class prg cls'
        | _ -> assert false
    in
      List.fold_left f program updates.decls

end
