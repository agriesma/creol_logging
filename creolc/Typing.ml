(*
 * Typing.ml -- Type analysis for Creol.
 *
 * This file is part of creoltools
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

(*s This module implements the type checker for Creol.

  Because {\Creol} features recursive types (interfaces may accept
  values of themselves), sub-typing, and method overloading, the formal
  theory of these types corresponds to System
  $F^{\omega}_{\wedge}$~\cite{compagnoni96:_inter_types_multip_inher}.
  For this particular theory, type reconstruction is generally
  undecidable~\citelist{\cite{pierce94:_bound_quant_undec}
  \cite{compagnoni04:_higher_order_subty_decid}}.

  The central ideas of this implementation are derived from Cardelli's
  implementation of $F_{<:}$, which he has described
  in~\cite{cardelli93:_implem_f}.  Using this algorithm, the type
  checker may reject some well-typed programs, because it fails to
  guess right, leading to sometimes puzzling error messages.  In
  practice, these situations do not occur often.

*)

open Creol
open Expression
open Statement


(* Report messages from this module. *)

let log l = Messages.message (l + 2)


(* Our type environment is just a mapping from names, represented as
   strings, to types. We do not expect many elements in this
   environment, so a Map should provide the cleanest solution. *)

module Env = Map.Make(String)


(* The type checker raises an [Type_error (file, line, reason)]
   exception if it has deduced that an expression is not well-typed.
   The first two arguments refer to the file and line in which the
   error is occurring.  The third argument indicates the reason of the
   type error. *)

exception Type_error of string * int * string


(* This exception is raised by the unifier.  The argument is the
   constrained which cannot be resolved. *)


exception Unify_failure of Type.t * Type.t


(* Generate a new fresh variable name. *)

let fresh_var f =
  let Misc.FreshName(n, f') = f () in
    (Type.Variable n, f')


(* Pretty-print a constraint set. *)

let rec string_of_constraint_set =
  function
      [] -> "none"
    | [(s, t)] ->
        (Type.as_string s) ^ " <: " ^ (Type.as_string t)
    | (s, t)::l ->
        (Type.as_string s) ^ " <: " ^ (Type.as_string t) ^ ", " ^
	  (string_of_constraint_set l)


(* Determine whether a substitution is more specific than another one.
   A substitution $s$ is more specific than a substitution $t$, if $s$
   and $t$ have the same support (i.e., they substitute the same
   variables), and that for each $v$ in this support, we have $s<:t$.
*)

let subst_more_specific_p program s t =
  let keys = Type.Subst.fold (fun k _ a -> k::a) s [] in
  let p k =
    Program.subtype_p program (Type.Subst.find k s) (Type.Subst.find k t)
  in
    List.for_all p keys


(* Find a \emph{most specific solution} from a list of possible
   solutions.  The solution need not be unique.  If there is more than
   one most specific solution, an undetermined one is returned.  The
   chosen one need not be the one that proves type correctness.
*)

let find_most_specific program substs =
  List.fold_left
    (fun s t -> if subst_more_specific_p program s t then s else t)
    (List.hd substs)
    (List.tl substs)


(* Compute the most general unifier for a constraint set [c].  The
   result is a mapping from variable names to types.
   
   The constraint set is usually a set of pair of types.  Such
   a constraint states that two types are equal in the current
   substitution. *)

let unify ~program ~constraints =
  let rec do_unify c (res: Type.t Type.Subst.t): Type.t Type.Subst.t =
    if c = [] then
      res
    else
      (* May be we can get better results if we can select the next constraint
         in a smarter manner. *)
      let (s, t) = List.hd c
      and d = List.tl c
      in
	log 2 ("unify: constraint " ^ (Type.as_string s) ^ " <: " ^
		  (Type.as_string t)) ;
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
			   get the "best" solution. *)
			find_most_specific program cands
		end
	  | (Type.Variable x, _) when (Type.sentence_p t) ->
	      (* In this case, `x is a lower bound, i.e., `x <: t .
		 This constraint is trivially satisfied by t, but there may
		 be multiple constraints on x, and we need to choose the
		 strongest one. *)
	      let p (v, w) = (v = s) && (Type.sentence_p w) in
	      let t' =
		  Program.meet program (t::(List.map snd (List.filter p d)))
	      and d' = List.filter (fun x -> not (p x)) d
	      in
	        log 1 ("unify: chose " ^ x ^ " as " ^ (Type.as_string t')) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x t' t1, Type.substitute x t' t2)) d')
		  (Type.Subst.add x t' res)
	  | (Type.Variable x, _) when not (Type.occurs_p x t) ->
	      (* In this case, `x is a lower bound, i.e., `x <: t, and t
		 contains free variables.  This constraint is trivially
		 satisfied by t and t des not have any meets in [program].  *)
	        log 1 ("unify: chose " ^ x ^ " as " ^ (Type.as_string t)) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x t t1, Type.substitute x t t2)) d)
		  (Type.Subst.add x t res)
	  | (_, Type.Variable x) when Type.sentence_p s ->

	      (* In this case, `x is an upper bound, i.e., t <: `x .
		 This constraint is trivially satisfied by t, but there may
		 be multiple constraints on x, and we need to choose the
		 strongest one. *)
	      let s' =
		let p (v, w) = (w = t) && (Type.sentence_p v) in
		  Program.join program (List.map fst (List.filter p c))
	      in
	      let try_unify r =
	        log 1 ("try_unify: " ^ (Type.as_string r) ^ " for `" ^ x) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x r t1, Type.substitute x r t2)) d)
		  (Type.Subst.add x r res)
	      in
		begin
		  try
		    try_unify s'
		  with
		      Unify_failure _ ->
			  (* Try some supertype of t.

			     FIXME: For now we just choose Data, the top type.
			     We might try something smarter, however. *)
	                  log 1
			    ("try_unify: did not work, use Data for `" ^ x) ;
	                  try_unify Type.data
		end
	  | (_, Type.Variable x) when not (Type.occurs_p x s) ->

	      (* If s has free variables and x does not occur in s,
		 then we choose x to be s, and if this failes, we
		 try Any and then Data, since we cannot guess
		 something better. *)

	      let try_unify r =
	        log 1 ("try_unify: " ^ (Type.as_string r) ^ " for `" ^ x) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x r t1, Type.substitute x r t2)) d)
		  (Type.Subst.add x r res)
	      in
		begin
		  try
		    try
		      try_unify s
		    with
			Unify_failure _ -> try_unify Type.any
		  with
		      Unify_failure _ -> try_unify Type.data
		end
	  | (_, Type.Basic "Data") ->
	      (* Every type is supposed to be a subtype of data,
		 therefore this constraint is always true. *)
	      do_unify d res
	  | _ ->
		log 1 ("unify: failed to unify " ^
				    (Type.as_string s) ^ " as subtype of " ^
				    (Type.as_string t)) ;
		raise (Unify_failure (s, t))
  in
    log 1 "\n=== unify ===" ;
    let res = do_unify constraints (Type.Subst.empty) in
      log 1 "=== success ===\n" ; res


(* Type check a tree. *)

let typecheck tree: Program.t =
  let error_ambigous note name callee_t cands =
    let f m = "    " ^ (Method.name_as_string m) in
    let rec g = function
      | [] -> assert false
      | [m] -> f m
      | m::l -> (f m) ^ "\n" ^ (g l)
    in
    let tmp = g cands in
      raise (Type_error (note.file, note.line,
			 "Call to method " ^ name ^ " of " ^
			   (Type.as_string callee_t) ^
			   " is ambigous:\n" ^ tmp))
  in
  let type_check_expression program cls meth coiface constr expr =

    (* Type check an expression [expr] in the environment
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

    (* Reconstruct the type of an expression.

       [env] is a type environment.  It is represented as a hash
       table ([Env]) which maps names to types.  The environment
       will be updated by the binders [Forall], [Exists], and
       [Choose].  Looking up the type information of a name occurs
       in this order:
       \begin{enumerate}
       \item First, look in [env] to see whether the name is locally
       bound.
       \item Second, look in the scope of the current method.
       \item Last, look in the scope of the current class and its
       superclasses.
       \end{enumerate}

       [constr] is the current constraint set.

       [fresh_name] is a monad used for generating new names.

       The result of this function is to update the input expression
       with new type variable names and to compute a new constraint
       set.  The constraint set will be used to compute
       instantiations for the type variables in [unify].

       Return the expression with updated type annotations (in Pierce,
       this would be the type), the function generating a new fresh
       type variable, and the new constraint set.  *)

    let rec type_recon_expression env constr fresh_name =
      function
	  This n ->
	    (This (set_type n (Class.get_type cls)), constr, fresh_name)
	| QualifiedThis (n, t) ->
	    if Program.subtype_p program (Class.get_type cls) t then
	      (QualifiedThis (set_type n t, t), constr, fresh_name)
	    else
	      raise (Type_error (Expression.file n, Expression.line n,
			         "Cannot qualify this as " ^
				   (Type.as_string t)))
	| Caller n ->
	    (Caller (set_type n (Type.Basic coiface)), constr, fresh_name)
	| Null n ->
	    let (v, fresh_name') = fresh_var fresh_name in
	      (Null (set_type n v), constr, fresh_name')
	| Nil n ->
	    let (v, fresh_name') = fresh_var fresh_name in
	      (Nil (set_type n (Type.Application ("List", [v]))),
	       constr, fresh_name')
	| History n ->
	    (History (set_type n Type.history), constr, fresh_name)
	| Now n ->
	    (Now (set_type n Type.time), constr, fresh_name)
	| Bool (n, value) ->
	    (Bool (set_type n Type.bool, value), constr, fresh_name)
	| Int (n, value) ->
	    (Int (set_type n Type.int, value), constr, fresh_name)
	| Float (n, value) ->
	    (Float (set_type n Type.real, value), constr, fresh_name)
	| String (n, value) ->
	    (String (set_type n Type.string, value), constr, fresh_name)
	| Tuple (n, l) ->
	    let (l', constr', fresh_name') =
	      type_recon_expression_list env constr fresh_name l
	    in
	      (Tuple (set_type n (Type.Tuple (List.map get_type l')), l'),
	       constr', fresh_name')
	| ListLit (n, l) ->
	    let (l', constr', fresh_name') = 
	      type_recon_expression_list env constr fresh_name l in
	    let (v, fresh_name'') = fresh_var fresh_name' in
	    let ty = Type.Application ("List", [v]) in
	      (ListLit (set_type n ty, l'),
	       (List.map (fun e -> (get_type e, v)) l') @ constr',
	       fresh_name'')
	| SetLit (n, l) ->
	    let (l', constr', fresh_name') = 
	      type_recon_expression_list env constr fresh_name l in
	    let (v, fresh_name'') = fresh_var fresh_name' in
	    let ty = Type.set [v] in
	      (SetLit (set_type n ty, l'),
	       (List.map (fun e -> (get_type e, v)) l') @ constr',
	       fresh_name'')
	| Id (n, name) ->
	    let res =
	      try
		try
		  try
		    Env.find name env
		  with
		      Not_found ->
			(Method.find_variable meth name).VarDecl.var_type
		with Not_found ->
		  (Program.find_attr_decl program cls name).VarDecl.var_type
	      with
		  Not_found ->
		    raise (Type_error ((n.Expression.file),
				       (n.Expression.line),
				       "Identifier " ^ name ^
					 " not declared"))
	    in
	      (Id (set_type n res, name), constr, fresh_name)
	| StaticAttr (n, name, ((Type.Basic c) as t)) ->
	    let res =
	      Program.find_attr_decl program (Program.find_class program c)
		name
	    in
	      (StaticAttr (set_type n res.VarDecl.var_type, name, t),
	       constr, fresh_name)
	| StaticAttr _ -> assert false
	| Unary (n, op, arg) ->
	    let (arg', constr', fresh_name') =
	      type_recon_expression env constr fresh_name arg 
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
			(Function.domain_type candidate,
			 candidate.Function.result_type)
		    in
		      fresh_names_in_type fresh_name' r
		| candidates ->
		    let (fn'', t) =
		      List.fold_left (fun (fn, t) o ->
					let r =
					  Type.Function (Function.domain_type o,
							 o.Function.result_type)
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
	      type_recon_expression env constr fresh_name arg1
	    in
	    let (arg2', constr'', fresh_name'') =
	      type_recon_expression env constr' fresh_name' arg2
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
			(Function.domain_type candidate,
			 candidate.Function.result_type)
		    in
		      fresh_names_in_type fresh_name'' r
		| candidates ->
		    let (fn'', t) =
		      List.fold_left (fun (fn, t) o ->
					let r =
					  Type.Function (Function.domain_type o,
							 o.Function.result_type)
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
	    let (cond', constr', fresh_name') =
	      type_recon_expression env constr fresh_name cond
	    in
	    let  (iftrue', constr'', fresh_name'') =
	      type_recon_expression env constr' fresh_name' iftrue
	    in
	    let (iffalse', constr''', fresh_name''') =
	      type_recon_expression env constr'' fresh_name'' iffalse
	    in
	    let (rt, fresh_name'''') = fresh_var fresh_name'''  in
	      (Expression.If (set_type n rt, cond', iftrue', iffalse'),
	       [(get_type cond', Type.bool); (get_type iftrue', rt);
		(get_type iffalse', rt)] @ constr''', fresh_name'''')
	| FuncCall (n, name, args) ->
	    let (nargs, constr', fresh_name') =
	      type_recon_expression_list env constr fresh_name args 
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
			(Function.domain_type candidate,
			 candidate.Function.result_type)
		    in
		      fresh_names_in_type fresh_name' r
		| candidates ->
		    let (fn'', t) =
		      List.fold_left (fun (fn, t) o ->
					let r =
					  Type.Function (Function.domain_type o,
							 o.Function.result_type)
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
	    begin
	      try
		if Method.label_p meth name then
		  (Label (set_type n (Type.Basic "Bool"), l), constr,
		   fresh_name)
		else
		  raise (Type_error (Expression.file n, Expression.line n,
				     "Variable " ^ name ^
				       " is not of type Label"))
	      with
		  Not_found ->
		    raise (Type_error (Expression.file n, Expression.line n,
				       "Label " ^ name ^ " not declared"))
	    end
	| Label _ -> assert false
	| New (n, Type.Basic c, args) ->
	    let (args', constr', fresh_name') =
	      type_recon_expression_list env constr fresh_name args
	    in
	    let cls' =
	      try
		Program.find_class program c
	      with
		  Not_found ->
		    raise (Type_error (Expression.file n, Expression.line n,
				       "Class " ^ c ^ " not defined"))
	    in
	    let mk x y = (get_type x, y.VarDecl.var_type) in
	    let t =
	      try
		List.map2 mk args' cls'.Class.parameters
	      with
		  Invalid_argument _ ->
		    raise (Type_error (Expression.file n, Expression.line n,
				       "Arguments to new " ^ c ^
					 " mismatch in length"))
	    in
	      (New (set_type n (Class.get_type cls'), Type.Basic c, args'),
	       t@constr', fresh_name')
	| New _ -> assert false
	| Choose (n, v, t, e) ->

	    (* The rule for typing this expression is: The type of [e]
	       is \texttt{Bool} in an environment where [v] has type
	       [t]. Then the result type is [t]. *)

	    if Env.mem v env then
	      Messages.warn Messages.Shadow n.Expression.file n.Expression.line
		("Variable " ^ v ^ " hides a different variable") ;
	    let (e', constr', fresh_name') =
	      type_recon_expression (Env.add v t env) constr fresh_name e
	    in
	      (Choose (set_type n t, v, t, e'),
	       (get_type e', Type.bool)::constr', fresh_name')
	| Exists (n, v, t, e) ->

	    (* The rule for typing this expression is: The type of [e]
	       is \texttt{Bool} in an environment where [v] has type
	       [t]. Then the result type is \texttt{Bool}. *)

	    if Env.mem v env then
	      Messages.warn Messages.Shadow n.Expression.file n.Expression.line
		("Variable " ^ v ^ " hides a different variable") ;
	    let (e', constr', fresh_name') =
	      type_recon_expression (Env.add v t env) constr fresh_name e
	    in
	      (Exists (set_type n Type.bool, v, t, e'),
	       (get_type e', Type.bool)::constr', fresh_name')
	| Forall (n, v, t, e) ->
	    if Env.mem v env then
	      Messages.warn Messages.Shadow n.Expression.file n.Expression.line
		("Variable " ^ v ^ " hides a different variable") ;
	    let (e', constr', fresh_name') =
	      type_recon_expression (Env.add v t env) constr fresh_name e
	    in
	      (Forall (set_type n Type.bool, v, t, e'),
	       (get_type e', Type.bool)::constr', fresh_name')
	| Expression.Extern _ -> assert false
	| SSAId (n, name, version) ->
	    let res =
	      try
		try
		  Env.find name env
		with
		    Not_found ->
		      (Method.find_variable meth name).VarDecl.var_type
	      with
		  Not_found ->
		    raise (Type_error ((Expression.file n),
				       (Expression.line n),
				       "Identifier " ^ name ^ " not declared"))
	    in
	      (SSAId (set_type n res, name, version), constr, fresh_name)
	| Phi (n, args) ->
	    let (args', constr', fresh_name') =
	      type_recon_expression_list env constr fresh_name args
	    in
	    let ty' =
	      Program.meet program (List.map get_type args')
	    in
	      (Phi (set_type n ty', args'), constr', fresh_name')
    and type_recon_expression_list env constr fresh_name =
      function
	  [] -> ([], constr, fresh_name)
	| e::l ->
	    let (e', c', f') = type_recon_expression env constr fresh_name e in
	    let (l', c'', f'') = type_recon_expression_list env c' f' l in
	      (e'::l', c'', f'')
    in
    let (expr', constr', _) =
      type_recon_expression Env.empty constr
	(Misc.fresh_name_gen "_") expr
    in
    let subst =
      try
	let file = Expression.file (Expression.note expr)
	and line = string_of_int (Expression.line (Expression.note expr)) 
	in 
	  Messages.message 2
	    ("Unify expression in " ^ file ^ ":" ^ line) ;
	  unify program constr'
      with
	  Unify_failure (s, t) ->
	    let file = Expression.file (Expression.note expr)
	    and line = string_of_int (Expression.line (Expression.note expr)) 
	    in 
	      prerr_endline (file ^ ":" ^ line ^ ": expression has type " ^
			       (Type.as_string s) ^ " but expected is type " ^
			       (Type.as_string t) ^
			       "\n  Cannot satisfy constraints: " ^
			       (string_of_constraint_set constr')) ;
	      exit 1
    in
      substitute_types_in_expression subst expr'
  in
  let type_check_assertion program cls coiface meth e =
    let e' =
      type_check_expression program cls meth coiface [] e
    in
      if Type.bool_p (get_type e') then
	e'
      else
	raise (Type_error (Expression.file (Expression.note e'),
			   Expression.line (Expression.note e'),
			   "Expression is not of type Bool"))
  in
  let type_check_lhs program (cls: Class.t) meth coiface =
    function
	LhsId (n, name) ->
	  let res =
	    try
	      try
		(Method.find_variable meth name).VarDecl.var_type
	      with
		  Not_found ->
		    (Program.find_attr_decl program cls name).VarDecl.var_type
	    with
		Not_found ->
		  raise (Type_error ((Expression.file n),
				     (Expression.line n),
				     "Identifier " ^ name ^ " not declared"))
	  in
	    LhsId (set_type n res, name)
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
		  raise (Type_error ((Expression.file n),
				     (Expression.line n),
				     "Identifier " ^ name ^ " not declared"))
	  in
	    LhsSSAId (set_type n res, name, version)
  in
  let rec type_check_statement program cls meth coiface =

    (* Check all the constraints on method calls.  This is the generic
       rule. *)

    let check_method_call n label callee m (asco, _, _) ins outs =
      let (callee', callee_t) =
	let c = type_check_expression program cls meth coiface [] callee in
	  (c , Expression.get_type c)
      and (ins', ins_t) =
	let i =
	  List.map (type_check_expression program cls meth coiface []) ins
	in
	  (i, Some (List.map Expression.get_type i))
      and label' =
	match label with
	    None -> label
	  | Some l -> Some (type_check_lhs program cls meth coiface l)
      in
      let (outs', outs_t) =

	(* Here we have to guess a correct output type.  If [label]
	   has been provided, then [outs_t] must be [None] and get it
	   from the label. *)
	
	match (label', outs) with
	    (None, None) -> (None, None)
	  | (None, Some ol) ->
	      let o =
		List.map (type_check_lhs program cls meth coiface) ol
	      in
		(Some o, Some (List.map Expression.get_lhs_type o))
	  | (Some l, None) ->
	      (None, Some (Type.get_from_label (Expression.get_lhs_type l)))
	  | (Some _, Some _) -> assert false
      in
      let ifaces =
	try
	  match callee_t with
	    | Type.Intersection l ->
		List.map
		  (fun i -> Program.find_interface program (Type.name i)) l
	    | Type.Internal ->
		[]
	    | Type.Basic n | Type.Application (n, _) ->
		[Program.find_interface program n]
	    | _ ->
		assert false
	with
	    Not_found ->
	      raise (Type_error (n.file, n.line,
				 "Interface " ^ (Type.as_string callee_t) ^
				   " not defined."))
      in
      let co =
	let co' =
	  match asco with
	      None -> Class.get_type cls
	    | Some c -> 

		(* Make sure the provided cointerface is actually implemented
		   by the current class. *)
		
		if Program.subtype_p program (Class.get_type cls) c then
		  c
		else
		  raise (Type_error (n.file, n.line, (Type.as_string c) ^
				       " is not implemented by class " ^
				       cls.Class.name ^ " of type " ^
				       (Type.as_string (Class.get_type cls))))
	in
	let cands =
	  List.fold_left
	    (fun a iface ->
	       (Program.interface_find_methods program iface m
		  (Some co', ins_t, outs_t)) @ a)
	    [] ifaces
	in
	  match cands with
	      [] -> raise (Type_error (n.file, n.line,
				       "Interface " ^
					 (Type.as_string callee_t) ^
					 " does not provide a method " ^ m ^ 
					 " with signature " ^
					 (Type.string_of_sig
					    (Some co', ins_t, outs_t))))
	    | [meth] -> meth.Method.coiface
	    | _ -> error_ambigous n m callee_t cands
      in
	if (Program.contracts_p program cls co) then
	  (label', callee', (Some co, ins_t, outs_t), ins', outs')
	else
	  raise (Type_error (n.file, n.line,
	  		     "Class " ^ cls.Class.name ^
			       " does not contract interface " ^
			       (Type.as_string co)))
    in
    let check_async_method_call n label callee m sign ins =
      let (label', callee', sign', ins', _) =
	check_method_call n label callee m sign ins None
      in
	(label', callee', sign', ins')
    and check_sync_method_call n callee m sign ins outs =
      let (_, callee', sign', ins', outs') =
	check_method_call n None callee m sign ins (Some outs)
      in
	match outs' with
	    None -> assert false
	  | Some o -> (callee', sign', ins', o)
    in
    let check_method_bounds n m signature lb ub =
      let c' =
	match lb with
	    None -> cls
	  | Some x ->
	      if Program.subclass_p program cls.Class.name x then
		Program.find_class program x
	      else
	        raise (Type_error (n.file, n.line,
			           "Class " ^ x ^ " is not a subclass of " ^
				     cls.Class.name))
      in

        (* FIXME: We check for an internal method only, but in the
	   paper \emph{A Dynamic Binding Strategy ...} and the
	   authorisation policy example this mechanism is used to
	   access any method internally. *)

	match ub with
	    None -> 
	      if Program.class_provides_method_p program c' m signature then
		()
	      else
		raise (Type_error (n.file, n.line,
				   "Class " ^ c'.Class.name ^
				     " does not provide method " ^ m ^
				     (Type.string_of_sig signature)))
	  | Some y ->
	      let cands =
		Program.class_find_methods program c' m signature
	      in
	      let p m =
		Program.subclass_p program y m.Method.location
	      in
		if List.exists p cands then
		  ()
		else
		  raise (Type_error (n.file, n.line,
				     "Class " ^ c'.Class.name ^
				       " does not provide method " ^ m ^
				       "which is above " ^ y))
    in
    let check_local_async_call n m lb ub ins outs_t =
      let ins' =
	List.map (type_check_expression program cls meth coiface []) ins
      in
      let ins_t = List.map Expression.get_type ins' in
      let signature = (Some Type.Internal, Some ins_t, outs_t) in
      let () = check_method_bounds n m signature lb ub
      in (signature, ins')
    in
    let check_local_sync_call n m lb ub ins outs =
      let (ins', ins_t) =
	let i =
	  List.map (type_check_expression program cls meth coiface []) ins
	in
	  (i, List.map Expression.get_type i)
      and (outs', outs_t) =
	let o =
	  List.map (type_check_lhs program cls meth coiface) outs
	in
	  (o, List.map Expression.get_lhs_type o)
      in
      let signature = (Some Type.Internal, Some ins_t, Some outs_t) in
      let () = check_method_bounds n m signature lb ub in
	(signature, ins', outs')
    in
      function
	  Skip n -> Skip n
        | Release n -> Release n
        | Assert (n, e) ->
	    let e' = type_check_assertion program cls coiface meth e in
	      Assert (n, e')
        | Prove (n, e) ->
	    let e' = type_check_assertion program cls coiface meth e in
	      Prove (n, e')
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
		raise (Type_error (n.file, n.line,
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
		    raise (Type_error (n.file, n.line,
				       "Type mismatch in assignment: " ^ 
					 "length of arguments differ"))
	    in
	      Assign (n, lhs', rhs'')
        | Await (n, e) ->
	    let e' = type_check_assertion program cls coiface meth e in
	      Await (n, e')
        | Posit (n, e) ->
	    let e' = type_check_assertion program cls coiface meth e in
	      Posit (n, e')
        | AsyncCall (n, label, callee, m, sign, ins) ->
	    let (label', callee', sign', ins') =
	      check_async_method_call n label callee m sign ins
	    in
	      AsyncCall (n, label', callee', m, sign', ins')
        | Reply (n, label, retvals) -> 
	    let nlabel =
	      type_check_expression program cls meth coiface [] label
	    and nretvals =
	      List.map (type_check_lhs program cls meth coiface) retvals
	    in
	      if Program.subtype_p program
	        (Type.Tuple (List.map get_lhs_type nretvals))
	        (Type.Tuple (Type.get_from_label (Expression.get_type nlabel)))
	      then
	        Reply (n, nlabel, nretvals)
	      else
	        raise (Type_error (n.file, n.line, "Type mismatch"))
        | Free (n, args) -> assert false
        | Bury (n, args) -> assert false
        | LocalAsyncCall (n, None, m, _, lb, ub, args) ->
	    let (signature, args') =
	      check_local_async_call n m lb ub args None
	    in
	      LocalAsyncCall (n, None, m, signature, lb, ub, args')
        | LocalAsyncCall (n, Some label, m, _, lb, ub, args) ->
	    let l' = type_check_lhs program cls meth coiface label in
	    let lt = Type.get_from_label (Expression.get_lhs_type l') in
	    let (signature, args') =
	      check_local_async_call n m lb ub args (Some lt)
	    in
	      LocalAsyncCall (n, Some l', m, signature, lb, ub, args')
        | SyncCall (n, callee, m, sign, ins, outs) ->
	    let (callee', signature, ins', outs') =
	      check_sync_method_call n callee m sign ins outs
	    in
	      SyncCall (n, callee', m, signature, ins', outs')
        | AwaitSyncCall (n, callee, m, sign, ins, outs) ->
	    let (callee', sign', ins', outs') =
	      check_sync_method_call n callee m sign ins outs
	    in
	      AwaitSyncCall (n, callee', m, sign', ins', outs')
	| LocalSyncCall (n, m, _, lb, ub, ins, outs) ->
            let (signature, ins', outs') =
	      check_local_sync_call n m lb ub ins outs
	    in
              LocalSyncCall (n, m, signature, lb, ub, ins', outs')
	| AwaitLocalSyncCall (n, m, _, lb, ub, ins, outs) ->
            let (signature, ins', outs') =
	      check_local_sync_call n m lb ub ins outs
	    in
	      AwaitLocalSyncCall (n, m, signature, lb, ub, ins', outs')
	| Tailcall _ -> assert false
	| If (n, cond, iftrue, iffalse) ->
	    let cond' = type_check_assertion program cls coiface meth cond in
	      If (n, cond',
		  type_check_statement program cls meth coiface iftrue,
		  type_check_statement program cls meth coiface iffalse)
	| While (n, cond, inv, body) ->
	    let cond' = type_check_assertion program cls coiface meth cond
	    and inv' = type_check_assertion program cls coiface meth inv
	    in
	      While (n, cond', inv',
		     type_check_statement program cls meth coiface body)
	| DoWhile (n, cond, inv, body) ->
	    let cond' = type_check_assertion program cls coiface meth cond
	    and inv' = type_check_assertion program cls coiface meth inv
	    in
	      DoWhile (n, cond', inv',
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
    let () =
      let f d { VarDecl.name = n; var_type = t } =
	if not (Program.type_p program t) then
	  raise (Type_error (cls.Class.file, cls.Class.line,
			     "type " ^ (Type.as_string t) ^ " of " ^ d ^
			       " parameter " ^ n ^ " does not exist"))
      in
	List.iter (f "input") meth.Method.inpars ;
	List.iter (f "output") meth.Method.outpars
    in
    let m' = { meth with Method.vars = [] } in
    let r' = type_check_assertion program cls coiface m' meth.Method.requires
    and e' = type_check_assertion program cls coiface m' meth.Method.ensures
    and b' = match meth.Method.body with
	None -> None
      | Some s ->
	  Some (type_check_statement program cls meth coiface s)
    in
      if Type.bool_p (get_type r') then
	if Type.bool_p (get_type e') then
	  { meth with Method.requires = r'; ensures = e'; body = b' }
	else
	  raise (Type_error (Expression.file (Expression.note e'),
			     Expression.line (Expression.note e'),
			     "Post-condition is not Bool"))
      else
	raise (Type_error (Expression.file (Expression.note r'),
			   Expression.line (Expression.note r'),
			   "Pre-condition is not Bool"))
  and type_check_with_def program cls w =
    let coiface =
      match w.With.co_interface with
	| Type.Internal -> "" (* The co-interface may also be internal. *)
	| _ -> Type.name w.With.co_interface
    in
    let () =
      if not (Program.interface_p program w.With.co_interface) then
	raise (Type_error (cls.Class.file, cls.Class.line,
			   "cointerface " ^ coiface ^ " is not an interface"))
    in
    let i' =
      List.map (type_check_assertion program cls coiface Method.empty)
	w.With.invariants
    in
    let m' =
      List.map (type_check_method program cls coiface) w.With.methods
    in
      { w with With.methods = m'; invariants = i' }

  (* A class is well typed, if it provides methods for all the
     interfaces it claims to implement, if the initialisation of all
     attributes are well-typed, and if all with-declarations are
     well-typed.

     Type checking a class starts with checking, whether the class
     provides a method for each interface it declared.  *)
	
  and type_check_class program cls =

    let attribute_well_typed { VarDecl.name = n; var_type = t; init = i } =
      if Program.type_p program t then
	true
      else
	begin
	  Messages.error cls.Class.file cls.Class.line
	    ("type " ^ (Type.as_string t) ^ " of attribute " ^ n ^
	       " does not exist") ;
	  false
	end

    and parameter_well_typed { VarDecl.name = n; var_type = t } =
      if Program.type_p program t then
	true
      else
	begin
	  Messages.error cls.Class.file cls.Class.line
	    ("type " ^ (Type.as_string t) ^ " of class parameter " ^ n ^
	       " does not exist") ;
	  false
	end

    (* Count the number of message definitions missing for an interface. *)

    and methods_missing_for_iface i =
      let report m =
	Messages.error cls.Class.file cls.Class.line
	  (cls.Class.name ^ " does not provide a method " ^ m ^
	     " declared in " ^ i.Interface.name)
      in
      let methods_missing_for_with w = 
	let p m =
	  let s =
	    let d =
	      match Method.domain_type m with
		  Type.Tuple x -> x
		| _ -> assert false
	    in
	    let r = match Method.range_type m with 
		Type.Tuple x -> x 
	      | _ -> assert false
	    in
	      (Some w.With.co_interface, Some d, Some r)
	  in
	  let r =
	    Program.class_provides_method_p program cls m.Method.name s
	  in
	    if not r then report (m.Method.name ^ (Type.string_of_sig s)) ;
	    r
	in
	  List.fold_left (fun a m -> if (p m) then a else a + 1) 0
	    w.With.methods
      in
	List.fold_left (fun a w -> a + (methods_missing_for_with w)) 0
	  i.Interface.with_decls
    in
      try
	ignore (Program.superclasses program cls.Class.name) ;
	let () =
	  if (List.fold_left
		(fun a v -> if parameter_well_typed v then a else a + 1)
		0 cls.Class.parameters) > 0 then
	    exit 1
	in
	let () =
	  if (List.fold_left
		(fun a v -> if attribute_well_typed v then a else a + 1)
		0 cls.Class.attributes) > 0 then
	    exit 1
	in
	  begin
	    let methods_missing =
	      let c n =
		try
		  methods_missing_for_iface (Program.find_interface program n)
		with
		    Not_found ->
		      Messages.error cls.Class.file cls.Class.line
			("No interface " ^ n ^ " defined") ;
		      1
	      in
		try
		  List.fold_left (fun a n -> a + (c n)) 0 
                    (Program.class_implements program cls)
		with
	            Program.Interface_not_found (file, line, iface) ->
		      Messages.error file line ("Interface " ^ iface ^
						  " not found") ;
		      1
	    in
	      if (methods_missing = 0) then
		{ cls with Class.with_defs =
		    List.map (type_check_with_def program cls)
		      cls.Class.with_defs }
	      else
		exit 1
	  end
      with
	  Program.Class_not_found (f, l, c) ->
	    Messages.error f l ("Class " ^ c ^ " not defined") ;
	    exit 1

  and type_check_interface program iface =
    iface
  and type_check_declaration program =
    function
	Declaration.Class c ->
	  Declaration.Class (type_check_class program c)
      | Declaration.Interface i ->
	  Declaration.Interface (type_check_interface program i)
      | _ as d -> d
  in
  let rel = Program.compute_subtype_relation tree in
    if Program.acyclic_p rel then
      begin
	try
	  List.map (type_check_declaration tree) tree
	with
	    Type_error (file, line, msg) ->
	      Messages.error file line msg ;
	      exit 1
      end
    else
      begin
	let cycle = Program.find_cycle tree rel in
	  Messages.error "*top*" 0 ("subtype relation has a cycle: " ^
				      (Program.string_of_cycle cycle)) ;
	  exit 1
      end
