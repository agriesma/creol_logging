(*
 * CreolTyping.ml -- Type analysis for Creol.
 *
 * This file is part of creolcomp
 *
 * Written and Copyright (c) 2007
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

open Misc
open Creol
open Expression
open Statement

exception Type_error of string * int * string
exception Unify_failure of Type.t * Type.t

let fresh_var f =
  let FreshName(n, f') = f () in
    (Type.Variable n, f')

let rec string_of_constraint_set =
    function
        [] -> "none"
      | [(s, t)] ->
          (Type.as_string s) ^ " <: " ^ (Type.as_string t)
      | (s, t)::l ->
          (Type.as_string s) ^ " <: " ^ (Type.as_string t) ^ ", " ^
	    (string_of_constraint_set l)


let subst_more_specific_p program s t =
  (* Substitutions s and t must have the same support. *)
  let keys = Type.Subst.fold (fun k _ a -> k::a) s [] in
  let p k =
    Program.subtype_p program (Type.Subst.find k s) (Type.Subst.find k t)
  in
    List.for_all p keys

let find_most_specific program substs =
  List.fold_left
    (fun s t -> if subst_more_specific_p program s t then s else t)
    (List.hd substs)
    (List.tl substs)

let unify ~program ~constraints =
  let rec do_unify c (res: Type.t Type.Subst.t): Type.t Type.Subst.t =
    (** Compute the most general unifier for a constraint set [c].
	The result is a mapping from variable names to types.
	
	The constraint set is usually a set of pair of types.  Such
	a constraint states that two types are equal in the current
	substitution. *)
    if c = [] then
      res
    else
      let s = fst (List.hd c)
      and t = snd (List.hd c)
      and d = List.tl c
      in
	Messages.message 3 ("unify: " ^ (Type.as_string s) ^ " is subtype of " ^ (Type.as_string t)) ;
	match (s, t) with
	    (Type.Basic _, Type.Basic _) when Program.subtype_p program s t ->
		do_unify d res
	  | (Type.Tuple l1, Type.Tuple l2) when (List.length l1) = (List.length l2) ->
		do_unify ((List.combine l1 l2)@d) res
	  | (Type.Function (d1, r1), Type.Function (d2, r2)) ->
	      do_unify ((d1, d2)::(r2, r1)::d) res
	  | (Type.Application (s1, t1), Type.Application (s2, t2)) when s1 = s2 ->
	      do_unify ((List.combine t1 t2)@d) res
	  | (_, Type.Disjunction l) ->
	      (* This case is essentially handling operator
		 overloading, but we try to solve the general case,
		 here, anyhow, because this is probably simpler.

		 We find a solution to the constraint set if there
		 is one solution to the problem.  We will
		 therefore split the constraint set and try each
		 branch of the disjunction in sequence. *)
	      let rec try_unify_disjunctions =
		function
		    [] -> []
		  | x::r ->
		      try
			(do_unify ((s, x)::d) res) ::
			  (try_unify_disjunctions r)
		      with
			  Unify_failure _ -> (try_unify_disjunctions r)
	      in
		begin
		  match try_unify_disjunctions l with
		      [] -> raise (Unify_failure (s, t))
		    | [r] -> r
		    | cands ->
			(* The solution is ambigous, and we want to
			   get the "best" solution.

			   FIXME: If there is more than one best solution
			   one solution is guessed, which is probably
			   wrong. *)
			find_most_specific program cands
		end
	  | (Type.Variable x, _) when not (Type.occurs_p x t) ->
	      (* In this case, `x is a lower bound, i.e., `x <: t .
		 This constraint is trivially satisfied by t, but there may
		 be multiple constraints on x, and we need to choose the
		 strongest one. *)
	      let t' =
		Program.meet program (List.map snd
				       (List.filter (fun (v, _) -> (v = s)) c))
	      in
	        Messages.message 2 ("unify: chose " ^ x ^ " as " ^
				    (Type.as_string t')) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x t t1, Type.substitute x t t2)) d)
		  (Type.Subst.add x t res)
	  | (_, Type.Variable x) when not (Type.occurs_p x s) ->
	      (* In this case, `x is an upper bound, i.e., t <: `x .
		 This constraint is trivially satisfied by t, but there may
		 be multiple constraints on x, and we need to choose the
		 strongest one. *)
	      let t' = t
		(* Program.join program (List.map snd
			     (List.filter (fun (_, v) -> (v = t)) c)) *)
	      in
	      let try_unify r =
	        Messages.message 2 ("try_unify: " ^ (Type.as_string r) ^ " for `" ^ x) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x r t1, Type.substitute x r t2)) d)
		  (Type.Subst.add x r res)
	      in
		begin
		  try
		    try_unify t'
		  with
		      Unify_failure _ ->
			  (* Try some supertype of t.

			     FIXME: For now we just choose Data, the top type.
			     We might try something smarter, however. *)
	                  Messages.message 2
			    ("try_unify: did not work, use Data for `" ^ x) ;
	                  try_unify (Type.Basic "Data")
		end
	  | (_, Type.Basic "Data") ->
	      (* Every type is supposed to be a subtype of data,
		 therefore this constraint is always true. *)
	      do_unify d res
	  | _ ->
		Messages.message 2 ("unify: failed to unify " ^
				    (Type.as_string s) ^ " as subtype of " ^
				    (Type.as_string t)) ;
		raise (Unify_failure (s, t))
  in
    Messages.message 2 "\n=== unify ===" ;
    let res = do_unify constraints (Type.Subst.empty) in
      Messages.message 2 "=== success ===\n" ; res

let typecheck tree: Declaration.t list =
  let rec substitute_types_in_expression subst expr =
    let subst_in_note subst note =
      { note with Expression.ty =
	  Type.apply_substitution subst note.Expression.ty }
    in
      match expr with
	  This n ->
	    This (subst_in_note subst n)
	| QualifiedThis (n, t) ->
	    QualifiedThis (subst_in_note subst n,
			  Type.apply_substitution subst t)
	| Caller n ->
	    Caller (subst_in_note subst n)
	| Null n ->
	    Null (subst_in_note subst n)
	| Nil n ->
	    Nil (subst_in_note subst n)
	| Now n ->
	    Now (subst_in_note subst n)
	| Bool (n, value) ->
	    Bool (subst_in_note subst n, value)
	| Int (n, value) ->
	    Int (subst_in_note subst n, value)
	| Float (n, value) ->
	    Float (subst_in_note subst n, value)
	| String (n, value) ->
	    String (subst_in_note subst n, value)
	| Tuple (n, l) ->
	    Tuple (subst_in_note subst n,
		  List.map (substitute_types_in_expression subst) l)
	| ListLit (n, l) ->
	    ListLit (subst_in_note subst n,
		    List.map (substitute_types_in_expression subst) l)
	| SetLit (n, l) ->
	    SetLit (subst_in_note subst n,
		   List.map (substitute_types_in_expression subst) l)
	| Id (n, name) ->
	    Id (subst_in_note subst n, name)
	| StaticAttr (n, name, t) ->
	    StaticAttr (subst_in_note subst n, name, t)
	| Unary (n, op, arg) ->
	    Unary (subst_in_note subst n, op,
		  substitute_types_in_expression subst arg)
	| Binary (n, op, arg1, arg2) ->
	    Binary (subst_in_note subst n, op,
		   substitute_types_in_expression subst arg1,
		   substitute_types_in_expression subst arg2)
	| FuncCall (n, name, args) ->
	    FuncCall (subst_in_note subst n, name,
		     List.map (substitute_types_in_expression subst) args)
	| Expression.If (n, cond, iftrue, iffalse) ->
	    Expression.If (subst_in_note subst n,
			  substitute_types_in_expression subst cond,
			  substitute_types_in_expression subst iftrue,
			  substitute_types_in_expression subst iffalse)
	| Label (n, l) ->
	    Label (subst_in_note subst n,
		  substitute_types_in_expression subst l)
	| New (n, t, args) ->
	    New (subst_in_note subst n, Type.apply_substitution subst t,
		List.map (substitute_types_in_expression subst) args)
	      (*	| Choose (n, i, t, e) ->
			Choose (subst_in_note subst n, i,
			Type.apply_substitution subst t,
			substitute_types_in_expression subst e)
			| Forall (n, i, t, e) ->
			Forall (subst_in_note subst n, i,
			Type.apply_substitution subst t,
			substitute_types_in_expression subst e)
			| Exists (n, i, t, e) ->
			Exists (subst_in_note subst n, i,
			Type.apply_substitution subst t,
			substitute_types_in_expression subst e) *)
	| Expression.Extern _ -> assert false
	| SSAId (n, name, version) ->
	    SSAId (subst_in_note subst n, name, version)
	| Phi (n, args) ->
	    Phi (subst_in_note subst n,
		List.map (substitute_types_in_expression subst) args)
  in
  let type_check_expression program cls meth coiface constr expr =
    (** Type check an expression [expr] in the environment
	[program cls meth coiface] and the constraint set [constr] by
	first reconstructing the types and then unification.

	For ML like type systems a constraint set is usually a set of
	equalities on types, i.e., each constraint looks like [s = t].
	Here, we use inequalities of the form [s <= t] to represent a
	constraint in the set.  *)
    let fresh_names_in_type fresh_name t =
      let fv = Type.free_variables t in
      let (fresh_name', s) =
	List.fold_left
	  (fun (fn, s) x ->
	    let (v, fn') = fresh_var fn in
	      (fn', Type.Subst.add x v s))
	  (fresh_name, Type.Subst.empty)
	  fv
      in
	(fresh_name', Type.apply_substitution s t)
    in
    let rec type_recon_expression constr fresh_name =
      (** Reconstruct the type of an expression.

	  Return the expression with updated type annotations (in Pierce,
	  this would be the type), the function generating a new fresh
	  type variable, and the new constraint set.  *)
      function
	  This n ->
	    (This (set_type n (Class.get_type cls)), constr, fresh_name)
	| QualifiedThis (n, t) ->
	    (QualifiedThis (set_type n t, t), constr, fresh_name)
	| Caller n ->
	    (Caller (set_type n (Type.Basic coiface)), constr, fresh_name)
	| Null n ->
	    let (v, fresh_name') = fresh_var fresh_name in
	      (Null (set_type n v), constr, fresh_name')
	| Nil n ->
	    let (v, fresh_name') = fresh_var fresh_name in
	      (Nil (set_type n (Type.Application ("List", [v]))), constr, fresh_name')
	| Now n ->
	    (Now (set_type n (Type.Basic "Time")), constr, fresh_name)
	| Bool (n, value) ->
	    (Bool (set_type n (Type.Basic "Bool"), value), constr, fresh_name)
	| Int (n, value) ->
	    (Int (set_type n (Type.Basic "Int"), value), constr, fresh_name)
	| Float (n, value) ->
	    (Float (set_type n (Type.Basic "Float"), value), constr, fresh_name)
	| String (n, value) ->
	    (String (set_type n (Type.Basic "String"), value), constr, fresh_name)
	| Tuple (n, l) ->
	    let (l', constr', fresh_name') =
	      type_recon_expression_list constr fresh_name l
	    in
	      (Tuple (set_type n (Type.Tuple (List.map get_type l')), l'),
	      constr', fresh_name')
	| ListLit (n, l) -> 
	    let (l', constr', fresh_name') = 
	      type_recon_expression_list constr fresh_name l in
	    let (v, fresh_name'') = fresh_var fresh_name' in
	    let ty = Type.Application ("List", [v]) in
	      (ListLit (set_type n ty, l'),
	       (List.map (fun e -> (get_type e, v)) l') @ constr',
	       fresh_name'')
	| SetLit (n, l) ->
	    let (l', constr', fresh_name') = 
	      type_recon_expression_list constr fresh_name l in
	    let (v, fresh_name'') = fresh_var fresh_name' in
	    let ty = Type.Application ("Set", [v]) in
	      (SetLit (set_type n ty, l'),
	       (List.map (fun e -> (get_type e, v)) l') @ constr',
	       fresh_name'')
	| Id (n, name) ->
	    let res =
	      try
		(Method.find_variable meth name).VarDecl.var_type
	      with
		  Not_found ->
		    try
		      (Program.find_attr_decl program cls name).VarDecl.var_type
		    with
			Not_found ->
			  raise (Type_error ((Expression.file n),
					    (Expression.line n),
					    "Identifier " ^ name ^
					      " not declared"))
	    in
	      (Id (set_type n res, name), constr, fresh_name)
	| StaticAttr (n, name, (Type.Basic c)) ->
	    let res =
	      Program.find_attr_decl program (Program.find_class program c) name
	    in
	      (StaticAttr (set_type n res.VarDecl.var_type, name, (Type.Basic c)), constr, fresh_name)
	| StaticAttr _ -> assert false
	| Unary (n, op, arg) ->
	    let (arg', constr', fresh_name') =
	      type_recon_expression constr fresh_name arg 
	    in
	    let name = string_of_unaryop op in
	    let (fresh_name'', ty1) =
	      match Program.find_functions program name with
		  [] ->
		    raise (Type_error (Expression.file n, Expression.line n,
				      "Unary operator " ^ name ^
					" not defined"))
		| [candidate] ->
		    (* This is a small optimisation. *)
		    let r =
		      Type.Function
			(Operation.domain_type candidate,
			candidate.Operation.result_type)
		    in
		      fresh_names_in_type fresh_name' r
		| candidates ->
		    let (fn'', t) =
		      List.fold_left (fun (fn, t) o ->
			let r =
			  Type.Function (Operation.domain_type o,
					o.Operation.result_type)
			in
			let (fn', sr) = fresh_names_in_type fn r in
			  (fn', sr::t))
			(fresh_name', [])
			candidates
		    in
		      (fn'', Type.Disjunction t)
	    in
	    let ty2 = Type.Tuple [get_type arg'] in
	    let (v, fresh_name''') = fresh_var fresh_name'' in
	      (Unary (set_type n v, op, arg'),
	      (Type.Function (ty2, v), ty1)::constr', fresh_name''')
	| Binary (n, op, arg1, arg2) ->
	    let (arg1', constr', fresh_name') =
	      type_recon_expression constr fresh_name arg1
	    in
	    let (arg2', constr'', fresh_name'') =
	      type_recon_expression constr' fresh_name' arg2
	    in
	    let name = string_of_binaryop op in
	    let (fresh_name''', ty1) =
	      match Program.find_functions program name with
		  [] ->
		    raise (Type_error (Expression.file n, Expression.line n,
				      "Binary operator " ^ name ^
					" not defined"))
		| [candidate] ->
		    (* This is a small optimisation. *)
		    let r =
		      Type.Function
			(Operation.domain_type candidate,
			candidate.Operation.result_type)
		    in
		      fresh_names_in_type fresh_name'' r
		| candidates ->
		    let (fn'', t) =
		      List.fold_left (fun (fn, t) o ->
			let r =
			  Type.Function (Operation.domain_type o,
					o.Operation.result_type)
			in
			let (fn', sr) = fresh_names_in_type fn r in
			  (fn', sr::t))
			(fresh_name'', [])
			candidates
		    in
		      (fn'', Type.Disjunction t)
	    in
	    let ty2 = Type.Tuple [get_type arg1'; get_type arg2'] in
	    let (v, fresh_name'''') = fresh_var fresh_name''' in
	      (Binary (set_type n v, op, arg1', arg2'),
	      (Type.Function (ty2, v), ty1)::constr'', fresh_name'''')
	| Expression.If (n, cond, iftrue, iffalse) ->
	    let (ncond, constr', fresh_name') =
	      type_recon_expression constr fresh_name cond
	    in let  (niftrue, constr'', fresh_name'') =
	      type_recon_expression constr' fresh_name' iftrue
	    in let (niffalse, constr''', fresh_name''') =
	      type_recon_expression constr'' fresh_name'' iffalse
	    in
		 if (Expression.get_type ncond) = Type.boolean then
		   let restype =
		     Program.meet program [get_type niftrue; get_type niffalse]
		   in
		     (Expression.If (set_type n restype, ncond, niftrue, niffalse),
		     constr''', fresh_name''')
		 else
		   raise (Type_error (Expression.file n, Expression.line n,
				     "Condition must be boolean"))
	| FuncCall (n, name, args) ->
	    let (nargs, constr', fresh_name') =
	      type_recon_expression_list constr fresh_name args 
	    in
	    let (fresh_name'', ty1) =
	      match Program.find_functions program name with
		  [] ->
		    raise (Type_error (Expression.file n, Expression.line n,
				      "Function " ^ name ^ " not defined"))
		| [candidate] ->
		    (* This is a small optimisation. *)
		    let r =
		      Type.Function
			(Operation.domain_type candidate,
			candidate.Operation.result_type)
		    in
		      fresh_names_in_type fresh_name' r
		| candidates ->
		    let (fn'', t) =
		      List.fold_left (fun (fn, t) o ->
			let r =
			  Type.Function (Operation.domain_type o,
					o.Operation.result_type)
			in
			let (fn', sr) = fresh_names_in_type fn r in
			  (fn', sr::t))
			(fresh_name', [])
			candidates
		    in
		      (fn'', Type.Disjunction t)
	    in
	    let ty2 = Type.Tuple (List.map get_type nargs) in
	    let (v, fresh_name''') = fresh_var fresh_name'' in
	      (FuncCall (set_type n v, name, nargs),
	      (Type.Function (ty2, v), ty1)::constr', fresh_name''')
	| Label (n, (Id (_, name) | SSAId(_, name, _) as l)) ->
	    let exists =
	      try
		match Method.find_variable meth name with _ -> true
	      with
		  Not_found -> false
	    in
	      if exists then
		(Label (set_type n (Type.Basic "Bool"), l), constr, fresh_name)
	      else
		raise (Type_error (Expression.file n, Expression.line n,
				  "Label " ^ name ^ " not declared"))
	| Label _ -> assert false
	| New (n, Type.Basic c, args) ->
	    let (nargs, constr', fresh_name') =
	      type_recon_expression_list constr fresh_name args
	    in
	    let args_t = Type.Tuple (List.map get_type nargs) in
	    let cls_n =
	      try
		Program.find_class program c
	      with
		  Not_found ->
		    raise (Type_error (Expression.file n, Expression.line n,
				      "Class " ^ c ^ " not defined"))
	    in
	    let ctor_t = Type.Tuple
	      (List.map (fun x -> x.VarDecl.var_type) cls_n.Class.parameters)
	    in
	      if
		Program.subtype_p program args_t ctor_t
	      then
		(* BOGUS *)
		(New (set_type n (Class.get_type (Program.find_class program c)),
		     Type.Basic c, nargs), constr', fresh_name')
	      else
		raise (Type_error (Expression.file n, Expression.line n,
				  "Arguments to new " ^ c ^
				    " mismatch: expected " ^
				    (Type.as_string ctor_t) ^ " but got " ^
				    (Type.as_string args_t)))
	| New _ -> assert false
	| Expression.Extern _ -> assert false
	| SSAId (n, name, version) ->
	    let res =
	      try
		(Method.find_variable meth name).VarDecl.var_type
	      with
		  Not_found ->
		    try
		      (Class.find_attr_decl cls name).VarDecl.var_type
		    with
			Not_found ->
			  raise (Type_error ((Expression.file n),
					    (Expression.line n),
					    "Identifier " ^ name ^
					      " not declared"))
	    in
	      (SSAId (set_type n res, name, version), constr, fresh_name)
	| Phi (n, args) ->
	    let (nargs, constr', fresh_name') =
	      type_recon_expression_list constr fresh_name args
	    in
	    let nty =
	      Program.meet program (List.map get_type nargs)
	    in
	      (Phi (set_type n nty, nargs), constr', fresh_name')
    and type_recon_expression_list constr fresh_name =
      function
	  [] -> ([], constr, fresh_name)
	| e::l ->
	    let (e', c', f') = type_recon_expression constr fresh_name e in
	    let (l', c'', f'') = type_recon_expression_list c' f' l in
	      (e'::l', c'', f'')
    in
    let (expr', constr', _) =
      type_recon_expression constr (fresh_name_gen "_") expr
    in
    let subst =
      try
	unify program constr'
      with
	  Unify_failure (s, t) ->
	    let file = Expression.file (Expression.note expr)
	    and line = string_of_int (Expression.line (Expression.note expr)) 
	    in 
	      prerr_endline (file ^ ":" ^ line ^ ": expression has type " ^
			       (Type.as_string s) ^ " but expected is type " ^
			       (Type.as_string t) ^
			       ".\n  Cannot satisfy constraints: " ^
	                       (string_of_constraint_set constr')) ;
	      exit 1
    in
      substitute_types_in_expression subst expr'
  in
  let type_check_lhs program (cls: Class.t) meth coiface =
    function
	LhsVar (n, name) ->
	  let res =
	    try
	      (Method.find_variable meth name).VarDecl.var_type
	    with
		Not_found ->
		  try
		    (Class.find_attr_decl cls name).VarDecl.var_type
		  with
		      Not_found ->
			raise (Type_error ((Expression.file n),
					  (Expression.line n),
					  "Identifier " ^ name ^
					    " not declared"))
	  in
	    LhsVar (set_type n res, name)
      | LhsAttr (n, name, (Type.Basic c)) ->
	  let res =
	    (Program.find_attr_decl program
		(Program.find_class program c) name).VarDecl.var_type
	  in
	    LhsAttr (set_type n res, name, (Type.Basic c))
      | LhsAttr _ -> assert false
      | LhsWildcard (n, None) ->
	  LhsWildcard(set_type n Type.data, None)
      | LhsWildcard (n, Some ty) ->
	  LhsWildcard(set_type n ty, Some ty)
      | LhsSSAId (n, name, version) ->
	  let res =
	    try
	      (Method.find_variable meth name).VarDecl.var_type
	    with
		Not_found ->
		  try
		    (Class.find_attr_decl cls name).VarDecl.var_type
		  with
		      Not_found ->
			raise (Type_error ((Expression.file n),
					  (Expression.line n),
					  "Identifier " ^ name ^
					    " not declared"))
	  in
	    LhsSSAId (set_type n res, name, version)
  in
  let rec type_check_statement program cls meth coiface =
    let check_async_method_call n label callee m ins =
      (* Check an asyncrhonous method call *)
      let callee' =
	type_check_expression program cls meth coiface [] callee
      and ins' =
	List.map (type_check_expression program cls meth coiface []) ins
      and label' =
	match label with
	    None -> label
	  | Some lab -> Some (type_check_lhs program cls meth coiface lab)
      in
      let callee_t = Expression.get_type callee'
      and ins_t = Type.Tuple (List.map Expression.get_type ins')
      and outs_t =
	match label' with
	    None -> Type.data
	  | Some lab' -> Type.get_from_label (Expression.get_lhs_type lab')
      in
      let iface = 
	try
	  Program.find_interface program (Type.as_string callee_t)
	with
	    Not_found ->
	      raise (Type_error (file n, line n,
				"Interface " ^ (Type.as_string callee_t) ^
				  " not defined."))
      in
      let co =
	(* Find the cointerface of our methods. *)
	let cands =
	  Program.interface_find_methods program iface m (Class.get_type cls)
	    ins_t outs_t
	in
	  match cands with
	      [] -> raise (Type_error (file n, line n,
				      "Interface " ^ (Type.as_string callee_t) ^
					" does not provide a method " ^ m ^ 
					" with inputs " ^
					(Type.as_string ins_t) ^
					" and outputs " ^
					(Type.as_string outs_t) ^
					" to " ^
					(Type.as_string (Class.get_type cls))))
	    | [meth] -> meth.Method.coiface
	    | _ -> raise (Type_error (file n, line n,
				     "Call to method " ^ m ^ " of interface " ^
				       (Type.as_string callee_t) ^
				       " is ambigous."))
      in
      let signature = (co, ins_t, outs_t)
      in
	if (Program.contracts_p program cls co) then
	  (label', callee', signature, ins')
	else
	  raise (Type_error (file n, line n,
	  		    "Class " ^ cls.Class.name ^
			      " does not contract interface " ^
			      (Type.as_string co)))
    and check_sync_method_call n callee m ins outs =
      (* Check an asyncrhonous method call *)
      let callee' =
	type_check_expression program cls meth coiface [] callee
      and ins' =
	List.map (type_check_expression program cls meth coiface []) ins
      and outs' =
	List.map (type_check_lhs program cls meth coiface) outs
      in
      let callee_t = Expression.get_type callee'
      and ins_t = Type.Tuple (List.map Expression.get_type ins')
      and outs_t = Type.Tuple (List.map Expression.get_lhs_type outs')
      in
      let iface = 
	try
	  Program.find_interface program (Type.as_string callee_t)
	with
	    Not_found ->
	      raise (Type_error (file n, line n,
				"Interface " ^ (Type.as_string callee_t) ^
				  " not defined."))
      in
      let co =
	(* Find the cointerface of our methods. *)
	let cands =
	  Program.interface_find_methods program iface m (Class.get_type cls)
	    ins_t outs_t
	in
	  match cands with
	      [] -> raise (Type_error (file n, line n,
				      "Interface " ^ (Type.as_string callee_t) ^
					" does not provide a method " ^ m ^ 
					" with inputs " ^
					(Type.as_string ins_t) ^
					" and outputs " ^
					(Type.as_string outs_t) ^
					" to " ^
					(Type.as_string (Class.get_type cls))))
	    | [meth] -> meth.Method.coiface
	    | _ -> raise (Type_error (file n, line n,
				     "Call to method " ^ m ^ " of interface " ^
				       (Type.as_string callee_t) ^
				       " is ambigous."))
      in
      let signature = (co, ins_t, outs_t)
      in
	if (Program.contracts_p program cls co) then
	  (callee', signature, ins', outs')
	else
	  raise (Type_error (file n, line n,
	  		    "Class " ^ cls.Class.name ^
			      " does not contract interface " ^
			      (Type.as_string co)))
    in
      function
	  Skip n -> Skip n
        | Release n -> Release n
        | Assert (n, e) ->
	    Assert (n, type_check_expression program cls meth coiface [] e)
        | Prove (n, e) ->
	    Prove (n, type_check_expression program cls meth coiface [] e)
        | Assign (n, lhs, rhs) ->
	    let lhs' =
	      List.map (type_check_lhs program cls meth coiface) lhs
	    and rhs' =
	      List.map (type_check_expression program cls meth coiface []) rhs
	    in
	    let check_assignment_pair lhs rhs =
	      (* It has to be checked whether for each assignment part
		 we find a free type variable in the right-hand-side.
		 If this is the case we have to unify it with the type
		 of the left-hand-side.  On the left hand side the
		 type must not contain any free variables. *)
	      let lhs_t = Expression.get_lhs_type lhs
	      and rhs_t = Expression.get_type rhs in
	      let die () =
		raise (Type_error (file n, line n,
				  "Type mismatch in assignment: Expected " ^
				    (Type.as_string lhs_t) ^
				    " but got " ^
				    (Type.as_string rhs_t)))
	      in
		if Type.sentence_p rhs_t then
		  if Program.subtype_p program rhs_t lhs_t then
		    rhs
		  else
		    die ()
		else
		  let s =
		    try
		      unify program [(rhs_t, lhs_t)]
		    with
			Unify_failure _ -> die ()
		  in
		    substitute_types_in_expression s rhs
	    in
	    let rhs'' =
	      try
		List.map2 check_assignment_pair lhs' rhs'
	      with
		  Invalid_argument _ ->
		    raise (Type_error (file n, line n,
				      "Type mismatch in assignment: " ^ 
					"length of arguments differ"))
	    in
	      Assign (n, lhs', rhs'')
        | Await (n, e) ->
	    Await (n, type_check_expression program cls meth coiface [] e)
        | Posit (n, e) ->
	    Posit (n, type_check_expression program cls meth coiface [] e)
        | AsyncCall (n, label, callee, m, _, ins) ->
	    let (label', callee', signature, ins') =
	      check_async_method_call n label callee m ins
	    in
	      AsyncCall (n, label', callee', m, signature, ins')
        | Reply (n, label, retvals) -> 
	    let nlabel =
	      type_check_expression program cls meth coiface [] label
	    and nretvals =
	      List.map (type_check_lhs program cls meth coiface) retvals
	    in
	      if Program.subtype_p program
	        (Type.Tuple (List.map get_lhs_type nretvals))
	        (Type.get_from_label (Expression.get_type nlabel))
	      then
	        Reply (n, nlabel, nretvals)
	      else
	        raise (Type_error (file n, line n, "Type mismatch"))
        | Free (n, args) -> assert false
        | LocalAsyncCall (n, None, m, _, lb, ub, args) ->
	    (* FIXME:  Check the upper bound and lower bound constraints
	       for static resolution *)
	    let nargs =
	      List.map (type_check_expression program cls meth coiface []) args
	    in
	    let signature =
	      (Type.Internal,
	      Type.Tuple (List.map Expression.get_type nargs), Type.data)
	    in
	      (* A label value of none implies that the type if that
	         anonymous label is Label[Data]. *)
	      if Program.class_provides_method_p program cls m
	        (Type.Tuple (List.map get_type nargs)) Type.data
	      then
	        LocalAsyncCall (n, None, m, signature, lb, ub, nargs)
	      else
	        raise (Type_error (file n, line n,
			          "Class " ^ cls.Class.name ^
				    " does not provide method " ^ m))
        | LocalAsyncCall (n, Some label, m, _, lb, ub, args) ->
	    (* FIXME:  Check the upper bound and lower bound constraints
	       for static resolution *)
	    let nargs =
	      List.map (type_check_expression program cls meth coiface []) args
	    and nlabel =
	      type_check_lhs program cls meth coiface label
	    in
	    let signature =
	      (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	      (Type.get_from_label (Expression.get_lhs_type nlabel)))
	    in
	      if Program.class_provides_method_p program cls m
	        (Type.Tuple (List.map get_type nargs))
	        (Type.get_from_label (Expression.get_lhs_type nlabel))
	      then
	        LocalAsyncCall (n, Some nlabel, m, signature, lb, ub, nargs)
	      else
	        raise (Type_error (file n, line n,
			          "Class " ^ cls.Class.name ^
				    " does not provide method " ^ m))
        | SyncCall (n, callee, m, _, ins, outs) ->
	    let (callee', signature, ins', outs') =
	      check_sync_method_call n callee m ins outs
	    in
	      SyncCall (n, callee', m, signature, ins', outs')
        | AwaitSyncCall (n, callee, m, _, ins, outs) ->
	    let (callee', signature, ins', outs') =
	      check_sync_method_call n callee m ins outs
	    in
	      AwaitSyncCall (n, callee', m, signature, ins', outs')
	| LocalSyncCall (n, m, _, lb, ub, args, retvals) ->
	    (* FIXME:  Check the upper bound and lower bound constraints
	       for static resolution *)
	    let nargs =
	      List.map (type_check_expression program cls meth coiface [])
		args
	    and nouts =
	      List.map (type_check_lhs program cls meth coiface) retvals
	    in
	    let signature =
	      (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	      (Type.Tuple (List.map Expression.get_lhs_type nouts)))
		
	    in
	      if
		Program.class_provides_method_p program cls m
		  (Type.Tuple (List.map get_type nargs))
		  (Type.Tuple (List.map get_lhs_type nouts))
	      then
		LocalSyncCall (n, m, signature, lb, ub, nargs, nouts)
	      else
		raise (Type_error (file n, line n,
				  "Class " ^ cls.Class.name ^
				    " does not provide method " ^ m))
	| AwaitLocalSyncCall (n, m, _, lb, ub, args, retvals) ->
	    (* FIXME:  Check the upper bound and lower bound constraints
	       for static resolution *)
	    let nargs =
	      List.map (type_check_expression program cls meth coiface [])
		args
	    and nouts =
	      List.map (type_check_lhs program cls meth coiface) retvals
	    in
	    let signature =
	      (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	      (Type.Tuple (List.map Expression.get_lhs_type nouts)))
		
	    in
	      if
		Program.class_provides_method_p program cls m
		  (Type.Tuple (List.map get_type nargs))
		  (Type.Tuple (List.map get_lhs_type nouts))
	      then
		AwaitLocalSyncCall (n, m, signature, lb, ub, nargs, nouts)
	      else
		raise (Type_error (file n, line n,
				  "Class " ^ cls.Class.name ^
				    " does not provide method " ^ m))
	| Tailcall _ -> assert false
	| If (n, cond, iftrue, iffalse) ->
	    If (n, type_check_expression program cls meth coiface [] cond,
	       type_check_statement program cls meth coiface iftrue,
	       type_check_statement program cls meth coiface iffalse)
	| While (n, cond, None, body) ->
	    While (n, type_check_expression program cls meth coiface [] cond,
		  None,
		  type_check_statement program cls meth coiface body)
	| While (n, cond, Some inv, body) ->
	    While (n, type_check_expression program cls meth coiface [] cond,
		  Some (type_check_expression program cls meth coiface [] inv),
		  type_check_statement program cls meth coiface body)
	| Sequence (n, s1, s2) ->
	    let ns1 = type_check_statement program cls meth coiface s1 in
	    let ns2 = type_check_statement program cls meth coiface s2 in
	      Sequence (n, ns1, ns2)
	| Merge (n, s1, s2) ->
	    Merge (n, type_check_statement program cls meth coiface s1,
		  type_check_statement program cls meth coiface s2)
	| Choice (n, s1, s2) ->
	    Choice (n, type_check_statement program cls meth coiface s1,
		   type_check_statement program cls meth coiface s2)
	| Extern _ as s -> s
  and type_check_method program cls coiface meth =
    { meth with Method.body =
	match meth.Method.body with
	    None -> None
	  | Some s ->
	      Some (type_check_statement program cls meth coiface s) }
  and type_check_with_def program cls w =
    let coiface = Type.as_string w.With.co_interface
    in
      { w with With.methods =
	  List.map
	    (fun m -> type_check_method program cls coiface m)
	    w.With.methods }
  and type_check_class program cls =
    (* Compute the type environment within a class by adding first the class
       parameters to an empty hash table and then all attributes. *)
    { cls with Class.with_defs =
	List.map (type_check_with_def program cls) cls.Class.with_defs }
  and type_check_declaration program =
    function
	Declaration.Class c -> Declaration.Class (type_check_class program c)
      | _ as d -> d
  in
    try
      List.map (type_check_declaration tree) tree
    with
	Type_error (file, line, msg) -> Messages.error file line msg ; exit 1
