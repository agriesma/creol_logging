(* Creol.ml -- Definition and manipulation of Creol AST
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


(** Types *)
module Type =
  struct

    type t =
	(** The abstract syntax of types in Creol. *)
	Basic of string
	  (** A basic type. *)
	| Variable of string
	    (** A type variable. *)
	| Application of string * t list
	    (** A type application, e.g., [List[Int]]. *)
	| Tuple of t list
	    (** The type of a tuple. *)
	| Function of t list * t
	    (** The type of a function.  The first component refers to
		the annotation of the function tupe, the second
		component is a tuple describing the domain and the
		last component is the (unique) type of the function's
		range. *)
	| Structure of field list
	    (** The type of a structure. *)
	| Variant of field list
	    (** The type of a variant. *)
	| Intersection of t list
	    (** The type is an intersection type.  Intersection types
		do not have concrete syntax. *)
	| Union of t list
	    (** The type is a union type.  Union types do not have
		concrete syntax. *)
	| Internal
	    (** The co-interface of internal calls *)
    and field =
	(** The declaration of a field of a structure or a variant. *)
	{ field_name: string; (** Name of this field. *)
	  field_type: t (** Type of this field *)
	}


    let any = Basic "Any"

    let data = Basic "Data"

    let boolean = Basic "Bool"

    let label = "Label"

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
	| Function (d, r) ->
	    "[" ^ (string_of_creol_type_list d) ^ " -> " ^
		(as_string r) ^ "]"
	| Structure f -> "[# " ^ (string_of_field_list f) ^ " #]"
	| Variant f -> "[+ " ^ (string_of_field_list f) ^ " +]"
	| Intersection l -> "/* /\\ [" ^ (string_of_creol_type_list l) ^ "] */"
	| Union l -> "/* \\/ [" ^ (string_of_creol_type_list l) ^ "] */"
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

    let result_type =
      function
	  Function (_, r) -> r
	| _ -> assert false

    let get_from_label =
      function
	  Application ("Label", args) -> args
	| _ -> assert false

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

    let file note = note.file

    let line note = note.line

    let set_type note t = { note with ty = t }

    type t =
	  This of note
	| Caller of note
	| Now of note
	| Null of note
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
	| Label of note * t
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
	  This a -> a
	| Caller a -> a
	| Now a -> a
	| Null a -> a
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

    open Expression

    module IdSet = Set.Make(String)

    type note = {
	file: string;
	line: int;
	life: IdSet.t
    }

    let file note = note.file

    let line note = note.line

    let make_note pos = {
      file = pos.Lexing.pos_fname ;
      line = pos.Lexing.pos_lnum ;
      life = IdSet.empty 
    }

    type signature = Type.t * Type.t * Type.t

    let default_sig = (Type.any, Type.data, Type.data)

    type t =
      (** Abstract syntax of statements in Creol.  The type parameter ['a]
	  refers to the type of possible annotations. *)
	Skip of note
	| Release of note
	| Assert of note * Expression.t
	| Assign of note * Expression.lhs list * Expression.t list
	  (** A multiple assignment statement.  Requires that the two lists
	      are of the same length. *)
	| Await of note * Expression.t
	| Posit of note * Expression.t
	  (** A posit statement, which is used to define {i true} properties
              about time in a model. *)
	| AsyncCall of note * Expression.lhs option * Expression.t * string *
	   signature *  Expression.t list
	| Reply of note * Expression.t * Expression.lhs list
	| Free of note * Expression.t list
	| SyncCall of note * Expression.t * string * signature *
	    Expression.t list * Expression.lhs list
	| AwaitSyncCall of note * Expression.t * string * signature *
	    Expression.t list * Expression.lhs list
	| LocalAsyncCall of note * Expression.lhs option * string *
	    signature * string option * string option * Expression.t list
	| LocalSyncCall of note * string * signature * string option *
	    string option * Expression.t list * Expression.lhs list
	| AwaitLocalSyncCall of note * string * signature * string option *
	    string option * Expression.t list * Expression.lhs list
	| Tailcall of note * string * signature * string option *
	    string option * Expression.t list
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
	| Posit (a, _) -> a
	| AsyncCall (a, _, _, _, _, _) -> a
	| Reply (a, _, _) -> a
	| Free (a, _) -> a
	| SyncCall (a, _, _, _, _, _) -> a
	| AwaitSyncCall (a, _, _, _, _, _) -> a
	| LocalAsyncCall (a, _, _, _, _, _, _) -> a
	| LocalSyncCall (a, _, _, _, _, _, _) -> a
	| AwaitLocalSyncCall (a, _, _, _, _, _, _) -> a
	| Tailcall (a, _, _, _, _, _) -> a
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
	  (Release _ | Assert _ | Assign _ | Await _ | Posit _ | AsyncCall _ |
	   Reply _ | Free _ | SyncCall _ | AwaitSyncCall _ | LocalAsyncCall _ |
	   LocalSyncCall _ | AwaitLocalSyncCall _ | Tailcall _ |
	   Extern _) as s -> s
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

    let find_variable meth name =
      let find l = List.find (fun { VarDecl.name = n } -> n = name) l in
      try
	find meth.meth_vars
      with
	  Not_found ->
	    try
	      find meth.meth_inpars
	    with
		Not_found -> find meth.meth_outpars

  end





(** Abstract syntax of a with clause.

    A with clause consists of a co-interface name, a list of methods
    and a sequence of invariants. *)
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
	contracts: inherits list;
	implements: inherits list;
	attributes: VarDecl.t list;
	with_defs: With.t list }

  let get_type cls =
    let to_type inh = Type.Basic (fst inh) in
    let ifaces = cls.implements @ cls.contracts in
      if ifaces <> [] then
	Type.Intersection (List.map to_type ifaces)
      else
	Type.any

  let find_attr_decl cls name =
    let find l = List.find (function { VarDecl.name = n } -> n = name) l
    in
      try
	find cls.attributes
      with
	  Not_found -> find cls.parameters


  let contracts_p cls iface =
    if iface <> Type.any then
      List.exists (fun inh -> (fst inh) = (Type.as_string iface)) cls.contracts
    else
      true
	  
end





module Interface =
struct

  type inherits = string * Expression.t list

  type  t =
      { name: string;
	inherits: inherits list;
	with_decl: With.t list;
	hidden: bool }

  let cointerface iface =
      match (List.hd iface.with_decl).With.co_interface with
	  None -> Type.Internal
        | Some i -> Type.Basic i

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
      operations: Operation.t list;
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

end


module Program =
  struct
    type t = Declaration.t list

    let find_class ~program ~name =
      let class_with_name =
	function
	    Declaration.Class { Class.name = n } -> n = name
	  | _ -> false
      in
	match List.find class_with_name program with
	    Declaration.Class cls -> cls
	  | _ -> assert false

    let find_interface ~program ~name =
      let interface_with_name =
	function
	    Declaration.Interface { Interface.name = n } when n = name -> true
	  | _ -> false
      in
	match List.find interface_with_name program with
	    Declaration.Interface i -> i
	  | _ -> assert false

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

    let empty: (string, Type.t) Hashtbl.t = Hashtbl.create 1

    let rec subtype_p program gamma s t =
      (** Decides whether [s] is a subtype of [t] in [program]. *)
      (* FIXME: For simplicity we define subtype relation to be structural
         equality *)
      match (s, t) with
	  (_, Type.Basic "Data") -> true
	| (Type.Basic st, Type.Basic tt) ->
	    st = tt
	| (Type.Application (sc, sa), Type.Application (tc, ta)) ->
	    (subtype_p program gamma (Type.Basic sc) (Type.Basic tc)) &&
	      begin
		try 
		  List.for_all2 (subtype_p program gamma) sa ta
		with
		    Invalid_argument _ -> false
	      end
	| (Type.Tuple sa, Type.Tuple ta) ->
	    begin
	      try 
		(List.for_all2 (subtype_p program gamma) sa ta)
	      with
		  Invalid_argument _ -> false
	    end
	| (Type.Intersection sa, Type.Intersection ta) ->
	    List.exists
	      (fun s ->
		(List.for_all (fun t -> subtype_p program gamma s t) ta)) sa
	| (Type.Intersection sa, _) ->
	    List.exists (fun s -> subtype_p program gamma s t) sa
	| (Type.Union sa, Type.Union ta) -> assert false
	| (Type.Union sa, Type.Intersection ta) -> assert false
	| (Type.Union sa, _) ->
	    List.for_all (fun s -> subtype_p program gamma s t) sa
	| (Type.Internal, Type.Internal) -> true
	| (Type.Internal, _) -> false
	| (_, Type.Internal) -> false
    and promote program gamma =
      function
	  Type.Variable v ->
	      Hashtbl.find gamma v
	| Type.Application (s, t) -> Type.Application(s, t)
	| _ -> raise (Failure "promote")

    let meet ~program types =
      if (List.for_all (fun x -> (List.hd types) = x) types) then
	(List.hd types)
      else
	Type.data

    let find_functions ~program ~name =
      (** Find all definitions of a function called [name] in [program].
	  Returns the empty list if none is found. *)
      let all_operations =
	List.flatten
	  (List.map
	      (function
		  (Declaration.Datatype d) -> d.Datatype.operations
		| _ -> [])
	      program)
      in
	  List.filter (fun { Operation.name = n } -> (n = name))
	    all_operations

    exception Function_not_found of Operation.t list

    let find_function ~program ~name ~domain =
      (** Find the function [name] in [program], that matches
	  arguments of type [domain] best. Raises [Not_found] if no
	  such function can be found. *)
      let candidates = find_functions program name in
      let domains_match cand =
	try
	  List.for_all2 (fun s t -> subtype_p program empty s t)
	    domain
	    (List.map (fun p -> p.VarDecl.var_type) cand.Operation.parameters)
	with
	    Invalid_argument _ -> false
      in
	try
          List.find domains_match candidates
	with
	    Not_found -> raise (Function_not_found candidates)

    let interface_find_all ~program ~iface ~name coiface inputs outputs =
      (** Find all definitions of a method called [name] that matches
	  the signature [(coiface, inputs, outputs)] in [iface] and
	  its super-interfaces.  *)
      []

    let interface_provides_p ~program ~iface ~name coiface inputs outputs =
      (** Check whether the interface [iface] or one of its
	  superinterfaces provide a method matching the signature
	  [(coiface, inputs, outputs)]. *)
      (* FIXME: Take the signature into account. *)
      List.exists
	(fun w -> List.exists (fun m -> m.Method.meth_name = name)
	  w.With.methods)
	iface.Interface.with_decl

    let class_find_methods ~program ~cls meth ins outs =
      (** Find all definitions of a method called [name] that matches
	  the signature [(coiface, inputs, outputs)] in class [cls]
	  and its super-classes.  *)
      let rec find_methods_in_class c =
        let here =
	  List.flatten
	    (List.map
	        (fun w ->
		  List.filter (fun m -> m.Method.meth_name = meth)
		    w.With.methods) c.Class.with_defs)
        and supers = List.map fst c.Class.inherits
        in
	  List.fold_left
           (fun r i ->
             (find_methods_in_class (find_class program i))@r)
             here supers
    in
      find_methods_in_class cls

    let class_provides_method_p ~program ~cls meth ins outs =
      [] <> (class_find_methods program cls meth ins outs)

  end



(* XXX: This is a very ugly hack, but I need to discuss with Ingrid how
   I can get a hook into the type checker for a correct implementation
   of such a function and where we should put it. *)
let make_expr_note_from_stmt_note s =
	{ Expression.file = s.Statement.file;
	  Expression.line = s.Statement.line;
	  ty = Type.data }
