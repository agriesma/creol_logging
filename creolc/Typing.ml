(*
 * Typing.ml -- Type analysis for Creol.
 *
 * This file is part of creoltools
 *
 * Copyright (c) 2007, 2008 by Marcel Kyas <kyas@ifi.uio.no>
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

(** {2 Type checker}

  This module implements the type checker for Creol.

  Because Creol features recursive types (interfaces may accept
  values of themselves), sub-typing, and method overloading, the formal
  theory of these types corresponds to System
  {% $F^{\omega}_{\wedge}$ %}.
  For this particular theory, type reconstruction is generally
  undecidable.

  The central ideas of this implementation are derived from Cardelli's
  implementation of {% $F_{<:}$ %}, which he has described
  in  cardelli93:_implem_f.  Using this algorithm, the type
  checker may reject some well-typed programs, because it fails to
  guess right, leading to sometimes puzzling error messages.  In
  practice, these situations do not occur often.  *)

open Creol
open Expression
open Statement

(** Passes which must have been executed before this pass. *)
let dependencies = ""

(** Report messages from this module. *)

let log l = Messages.message (l + 2)


(** Our type environment is just a mapping from names, represented as
    strings, to types. We do not expect many elements in this
    environment, so a Map should provide the cleanest solution. *)
module Env = Map.Make(String)

type environment =
  { program: Program.t;
    cls: Class.t;
    meth: Method.t;
    env: Type.t Env.t;
  }

(** Method candidates are collected in a set. *)

module MSet = Set.Make(Method)


(** The type checker raises an [Type_error (file, line, reason)]
    exception if it has deduced that an expression is not well-typed.
    The first two arguments refer to the file and line in which the
    error is occurring.  The third argument indicates the reason of the
    type error. *)
exception Type_error of string * int * string


(** This exception is raised by the unifier.  The argument is the
    constrained which cannot be resolved. *)
exception Unify_failure of Type.t * Type.t


(** Generate a new fresh variable name. *)
let fresh_var f =
  let Misc.FreshName(n, f') = f () in
    (Type.Variable n, f')



(** Pretty-print a constraint set. *)
let rec string_of_constraint_set =
  function
      [] -> "none"
    | [(s, t)] ->
        (Type.string_of_type s) ^ " <: " ^ (Type.string_of_type t)
    | (s, t)::l ->
        (Type.string_of_type s) ^ " <: " ^ (Type.string_of_type t) ^ ", " ^
	  (string_of_constraint_set l)


(** {3 Unification} *)

(** Determine whether a substitution is more specific than another one.
    A substitution $s$ is more specific than a substitution $t$, if $s$
    and $t$ have the same support (i.e., they substitute the same
    variables), and that for each $v$ in this support, we have $s<:t$. *)
let subst_more_specific_p program s t =
  let keys = IdMap.fold (fun k _ a -> k::a) s [] in
  let p k =
    Program.subtype_p program (IdMap.find k s) (IdMap.find k t)
  in
    List.for_all p keys


(** Find a {e most specific solution} from a list of possible
    solutions.  The solution need not be unique.  If there is more than
    one most specific solution, an undetermined one is returned.  The
    chosen one need not be the one that proves type correctness.  *)
let find_most_specific program substs =
  List.fold_left
    (fun s t -> if subst_more_specific_p program s t then s else t)
    (List.hd substs)
    (List.tl substs)


(** Compute the most general unifier for a constraint set [c].  The
    result is a mapping from variable names to types.
   
    The constraint set is usually a set of pair of types.  Such
    a constraint states that two types are equal in the current
    substitution. *)
let unify ~program ~constraints =
  let rec do_unify c (res: Type.t IdMap.t): Type.t IdMap.t =
    if c = [] then
      res
    else
      (* May be we can get better results if we can select the next constraint
         in a smarter manner. *)
      let (s, t) = List.hd c
      and d = List.tl c
      in
	log 2 ("unify: constraint " ^ (Type.string_of_type s) ^ " <: " ^
		  (Type.string_of_type t)) ;
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
	        log 1 ("unify: chose " ^ x ^ " as " ^ (Type.string_of_type t')) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x t' t1, Type.substitute x t' t2)) d')
		  (IdMap.add x t' res)
	  | (Type.Variable x, _) when not (Type.occurs_p x t) ->
	      (* In this case, `x is a lower bound, i.e., `x <: t, and t
		 contains free variables.  This constraint is trivially
		 satisfied by t and t des not have any meets in [program].  *)
	        log 1 ("unify: chose " ^ x ^ " as " ^ (Type.string_of_type t)) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x t t1, Type.substitute x t t2)) d)
		  (IdMap.add x t res)
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
	        log 1 ("try_unify: " ^ (Type.string_of_type r) ^ " for `" ^ x) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x r t1, Type.substitute x r t2)) d)
		  (IdMap.add x r res)
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
	        log 1 ("try_unify: " ^ (Type.string_of_type r) ^ " for `" ^ x) ;
	        do_unify
		  (List.map
		      (fun (t1, t2) ->
		        (Type.substitute x r t1, Type.substitute x r t2)) d)
		  (IdMap.add x r res)
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
				    (Type.string_of_type s) ^ " as subtype of " ^
				    (Type.string_of_type t)) ;
		raise (Unify_failure (s, t))
  in
    let () = log 1 "\n=== unify ===" in
    let () = log 2 (string_of_constraint_set constraints) in
    let res = Type.normalise (do_unify constraints (IdMap.empty)) in
    let () = log 1 "=== success ===\n" in
      res


(** {3 Type reconstruction} *)

(** Replace each type variable in type [t] by a fresh name. Uses
    [fresh_name] to generate the variable.  *)
let fresh_names_in_type fresh_name t =
  let fv = Type.free_variables t in
  let (fresh_name', s) =
    Type.Vars.fold
      (fun x (fn, s) ->
	 let (v, fn') = fresh_var fn in (fn', IdMap.add x v s))
      fv
      (fresh_name, IdMap.empty)
  in
    (fresh_name', Type.apply_substitution s t)


(** Raise a type error exception for an expression note and a
    message. *)
let type_error note msg =
  raise (Type_error (note.Expression.file, note.Expression.line, msg))

(** Raise a type error exception, because identifier name is not
    declared. *)
let identifier_undeclared n name =
  type_error n ("Identifier " ^ name ^ " not declared")


(** Reconstruct the type of an expression.
    
    [env] is a type environment.  It is represented as a hash table
    ([Env]) which maps names to types.  The environment will be
    updated by the binders [Forall], [Exists], and [Choose].  Looking
    up the type information of a name occurs in this order:
    + First, look in [env] to see whether the name is locally bound
    + Second, look in the scope of the current method
    + Last, look in the scope of the current class and its superclasses
    
    [constr] is the current constraint set.
    
    [fresh_name] is a monad used for generating new names.
    
    The result of this function is to update the input expression
    with new type variable names and to compute a new constraint
    set.  The constraint set will be used to compute
    instantiations for the type variables in [unify].
    
    Return the expression with updated type annotations (in Pierce,
    this would be the type), the function generating a new fresh
    type variable, and the new constraint set. *)
let rec type_recon_expression env coiface constr fresh_name =
  function
      This n ->
	(This (set_type n (Class.get_type env.cls)), constr, fresh_name)
    | QualifiedThis (n, t) ->
	if Program.subtype_p env.program (Class.get_type env.cls) t then
	  (QualifiedThis (set_type n t, t), constr, fresh_name)
	else
	  type_error n ("Cannot qualify this as " ^ (Type.string_of_type t))
    | Caller n ->
	(Caller (set_type n (Type.Basic coiface)), constr, fresh_name)
    | Null n ->
	let (v, fresh_name') = fresh_var fresh_name in
	  (Null (set_type n v), constr, fresh_name')
    | Nil n ->
	let (v, fresh_name') = fresh_var fresh_name in
	  (Nil (set_type n (Type.list v)), constr, fresh_name')
    | History n ->
	(History (set_type n Type.history), constr, fresh_name)
    | Now n ->
	(Now (set_type n Type.time), constr, fresh_name)
    | Bool (n, value) ->
	(Bool (set_type n Type.bool, value), constr, fresh_name)
    | Int (n, value) ->
	(Int (set_type n Type.int, value), constr, fresh_name)
    | Float (n, value) ->
	(Float (set_type n Type.float, value), constr, fresh_name)
    | String (n, value) ->
	(String (set_type n Type.string, value), constr, fresh_name)
    | Tuple (n, l) ->
	let (l', constr', fresh_name') =
	  type_recon_expression_list env coiface constr fresh_name l
	in
	  (Tuple (set_type n (Type.Tuple (List.map get_type l')), l'),
	   constr', fresh_name')
    | ListLit (n, l) ->
	let (l', constr', fresh_name') = 
	  type_recon_expression_list env coiface constr fresh_name l in
	let (v, fresh_name'') = fresh_var fresh_name' in
	let ty = Type.list v in
	  (ListLit (set_type n ty, l'),
	   (List.map (fun e -> (get_type e, v)) l') @ constr', fresh_name'')
    | SetLit (n, l) ->
	let (l', constr', fresh_name') = 
	  type_recon_expression_list env coiface constr fresh_name l in
	let (v, fresh_name'') = fresh_var fresh_name' in
	let ty = Type.set v in
	  (SetLit (set_type n ty, l'),
	   (List.map (fun e -> (get_type e, v)) l') @ constr', fresh_name'')
    | MapLit (n, l) ->
	let (d, r) = List.split l in
	let (d', constr', fresh_name') = 
	  type_recon_expression_list env coiface constr fresh_name d in
	let (r', constr'', fresh_name'') =
	  type_recon_expression_list env coiface constr' fresh_name' r in
	let (dt, fresh_name''') = fresh_var fresh_name'' in
	let (rt, fresh_name'''') = fresh_var fresh_name''' in
	let ty = Type.map dt rt 
	and map t = List.map (fun e -> (get_type e, t)) in
	  (MapLit (set_type n ty, List.combine d' r'),
	   List.flatten [map dt d'; map rt r'; constr''], fresh_name'''')
    | Id (n, name) ->
	let res =
	  try
	    try
	      try
		Env.find name env.env
	      with
		  Not_found ->
		    (Method.find_variable env.meth name).VarDecl.var_type
	    with Not_found ->
	      (Program.find_attr_decl env.program env.cls name).VarDecl.var_type
	  with
	      Not_found ->
		identifier_undeclared n name
	in
	  (Id (set_type n res, name), constr, fresh_name)
    | StaticAttr (n, name, ((Type.Basic c) as t)) ->
	let res =
	  let program = env.program in 
	    Program.find_attr_decl program (Program.find_class program c)
	      name
	in
	  (StaticAttr (set_type n res.VarDecl.var_type, name, t),
	   constr, fresh_name)
    | StaticAttr _ -> assert false
    | Unary (n, op, arg) ->
	let (arg', constr', fresh_name') =
	  type_recon_expression env coiface constr fresh_name arg 
	in
	let name = string_of_unaryop op in
	let (fresh_name'', ty1) =
	  match Program.find_functions env.program name with
	      [] ->
		type_error n ("Unary operator " ^ name ^ " not defined")
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
	  type_recon_expression env coiface constr fresh_name arg1
	in
	let (arg2', constr'', fresh_name'') =
	  type_recon_expression env coiface constr' fresh_name' arg2
	in
	let name = string_of_binaryop op in
	let (fresh_name''', ty1) =
	  match Program.find_functions env.program name with
	      [] ->
		type_error n ("Binary operator " ^ name ^ " not defined")
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
	  type_recon_expression env coiface constr fresh_name cond
	in
	let  (iftrue', constr'', fresh_name'') =
	  type_recon_expression env coiface constr' fresh_name' iftrue
	in
	let (iffalse', constr''', fresh_name''') =
	  type_recon_expression env coiface constr'' fresh_name'' iffalse
	in
	let (rt, fresh_name'''') = fresh_var fresh_name'''  in
	  (Expression.If (set_type n rt, cond', iftrue', iffalse'),
	   [(get_type cond', Type.bool); (get_type iftrue', rt);
	    (get_type iffalse', rt)] @ constr''', fresh_name'''')
    | FuncCall (n, name, args) ->
	let (nargs, constr', fresh_name') =
	  type_recon_expression_list env coiface constr fresh_name args 
	in
	let (fresh_name'', ty1) =
	  match Program.find_functions env.program name with
	      [] ->
		type_error n ("Function " ^ name ^ " not defined")
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
	    if Method.future_p env.meth name then
	      (Label (set_type n Type.bool, l), constr,
	       fresh_name)
	    else
	      type_error n ("Variable " ^ name ^ " is not of type Label")
	  with
	      Not_found ->
		identifier_undeclared n name
	end
    | Label _ -> assert false
    | New (n, Type.Basic c, args) ->
	let (args', constr', fresh_name') =
	  type_recon_expression_list env coiface constr fresh_name args
	in
	let cls' =
	  try
	    Program.find_class env.program c
	  with
	      Not_found ->
		type_error n ("Class " ^ c ^ " not defined")
	in
	let mk x y = (get_type x, y.VarDecl.var_type) in
	let t =
	  try
	    List.map2 mk args' cls'.Class.parameters
	  with
	      Invalid_argument _ ->
		type_error n ("Arguments to new " ^ c ^ " mismatch in length")
	in
	  (New (set_type n (Class.get_type cls'), Type.Basic c, args'),
	   t@constr', fresh_name')
    | New _ -> assert false
    | Choose (n, v, t, e) ->
	
	(* The rule for typing this expression is: The type of [e]
	   is [Bool] in an environment where [v] has type
	   [t]. Then the result type is [t]. *)
	
	if Env.mem v env.env then
	  Messages.warn Messages.Shadow n.Expression.file n.Expression.line
	    ("Variable " ^ v ^ " hides a different variable") ;
	let (e', constr', fresh_name') =
	  type_recon_expression { env with env = (Env.add v t env.env) } coiface constr fresh_name e
	in
	  (Choose (set_type n t, v, t, e'),
	   (get_type e', Type.bool)::constr', fresh_name')
    | Exists (n, v, t, e) ->
	
	(* The rule for typing this expression is: The type of [e]
	   is {i Bool} in an environment where [v] has type
	   [t]. Then the result type is {i Bool}. *)
	
	if Env.mem v env.env then
	  Messages.warn Messages.Shadow n.Expression.file n.Expression.line
	    ("Variable " ^ v ^ " hides a different variable") ;
	let (e', constr', fresh_name') =
	  type_recon_expression { env with env = (Env.add v t env.env) } coiface constr fresh_name e
	in
	  (Exists (set_type n Type.bool, v, t, e'),
	   (get_type e', Type.bool)::constr', fresh_name')
    | Forall (n, v, t, e) ->
	if Env.mem v env.env then
	  Messages.warn Messages.Shadow n.Expression.file n.Expression.line
	    ("Variable " ^ v ^ " hides a different variable") ;
	let (e', constr', fresh_name') =
	  type_recon_expression { env with env = (Env.add v t env.env) } coiface constr fresh_name e
	in
	  (Forall (set_type n Type.bool, v, t, e'),
	   (get_type e', Type.bool)::constr', fresh_name')
    | Expression.Extern _ -> assert false
    | LabelLit (n, l) ->
	let (l', constr', fresh_name') = 
	  type_recon_expression_list env coiface constr fresh_name l in
	let (v, fresh_name'') = fresh_var fresh_name' in
	let ty = Type.future [v] in
	  (LabelLit (set_type n ty, l'),
	   (List.map (fun e -> (get_type e, v)) l') @ constr',
	   fresh_name'')
    | ObjLit _ -> assert false
    | SSAId (n, name, version) ->
	let res =
	  try
	    try
	      Env.find name env.env
	    with
		Not_found ->
		  (Method.find_variable env.meth name).VarDecl.var_type
	  with
	      Not_found ->
		identifier_undeclared n name
	in
	  (SSAId (set_type n res, name, version), constr, fresh_name)
    | Phi (n, args) ->
	let (args', constr', fresh_name') =
	  type_recon_expression_list env coiface constr fresh_name args
	in
	let ty' =
	  Program.meet env.program (List.map get_type args')
	in
	  (Phi (set_type n ty', args'), constr', fresh_name')
and type_recon_expression_list env coiface constr fresh_name =
  function
      [] -> ([], constr, fresh_name)
    | e::l ->
	let (e', c', f') = type_recon_expression env coiface constr fresh_name e in
	let (l', c'', f'') = type_recon_expression_list env coiface c' f' l in
	  (e'::l', c'', f'')


(** {3 Type checking} *)

let error_ambigous note name callee_t cands =
  let f m = "    " ^ (Method.name_as_string m) in
  let rec g = function
    | [] -> assert false
    | [m] -> f m
    | m::r -> (f m) ^ "\n" ^ (g r)
  in
  let tmp = g (MSet.elements cands) in
    raise (Type_error (note.file, note.line,
		       "Call to method " ^ name ^ " of " ^
			 (Type.string_of_type callee_t) ^
			 " is ambigous:\n" ^ tmp))


(** Type check an expression [expr] in the environment [program cls
    meth coiface] and the constraint set [constr] by first
    reconstructing the types and then unification.

    For ML like type systems a constraint set is usually a set of
    equalities on types, i.e., each constraint looks like [s = t].
    Here, we use inequalities of the form [s <= t] to represent a
    constraint in the set.  *)
let type_check_expression env coiface constr expr =
  let file = (Expression.note expr).Expression.file
  and line = (Expression.note expr).Expression.line
  and (expr', constr', _) =
    type_recon_expression env coiface constr
      (Misc.fresh_name_gen "_") expr
  in
  let subst =
    try
      let () = log 1 ("Unify expression in " ^ file ^ ":" ^ (string_of_int line)) in
        unify env.program constr'
    with
	Unify_failure (s, t) ->
	  raise (Type_error (file, line, "expression has type " ^
			       (Type.string_of_type s) ^
			       " but expected is type " ^
			       (Type.string_of_type t) ^
			       "\n  Cannot satisfy constraints: " ^
			       (string_of_constraint_set constr')))
  in
    let () = log 1 ("Substitution: " ^ (Type.string_of_substitution subst)) in
    let res = substitute_types_in_expression subst expr' in
    let () = log 1 ("Result: " ^ (Type.string_of_type (Expression.get_type res))) in
      res


let type_check_expression_list env coiface constr =
  function
      [] -> []
    | exprs ->
	let file = (Expression.note (List.hd exprs)).Expression.file
	and line = (Expression.note (List.hd exprs)).Expression.line
	and (exprs', constr', _) =
	  type_recon_expression_list env coiface constr
	    (Misc.fresh_name_gen "_") exprs
	in
	let subst =
	  try
	    Messages.message 2
	      ("Unify expression list in " ^ file ^ ":" ^
		 (string_of_int line));
	    unify env.program constr'
	  with
	      Unify_failure (s, t) ->
		raise (Type_error (file, line,
				   "expression has type " ^
				     (Type.string_of_type s) ^
				     " but expected is type " ^
				     (Type.string_of_type t) ^
				     "\n  Cannot satisfy constraints: " ^
				     (string_of_constraint_set constr')))
	in
          let () = log 1 ("Substitution: " ^ (Type.string_of_substitution subst)) in
          let res = List.map (substitute_types_in_expression subst) exprs' in
          let () = List.iter (fun e -> log 1 ("Result: " ^ (Type.string_of_type (Expression.get_type e)))) res in
            res


let type_check_assertion env coiface e =
  let e' =
    type_check_expression env coiface [] e
  in
    if Type.bool_p (get_type e') then
      e'
    else
      type_error (Expression.note e') "Expression is not of type Bool"


let type_check_lhs env coiface =
  function
      LhsId (n, name) ->
	let res =
	  try
	    try
	      (Method.find_variable env.meth name).VarDecl.var_type
	    with
		Not_found ->
		  (Program.find_attr_decl env.program env.cls name).VarDecl.var_type
	  with
	      Not_found ->
		identifier_undeclared n name
	in
	  LhsId (set_type n res, name)
    | LhsAttr (n, name, (Type.Basic c)) ->
	let res =
	  (Program.find_attr_decl env.program
	     (Program.find_class env.program c) name).VarDecl.var_type
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
	    (Method.find_variable env.meth name).VarDecl.var_type
	  with
	      Not_found ->
		identifier_undeclared n name
	in
	  LhsSSAId (set_type n res, name, version)


let rec type_check_statement env coiface =

  (* Check all the constraints on method calls.  This is the generic
     rule.

     First we check the type of the callee and determine the interface
     of [this].  *)

  let check_method_call n future callee m (asco, _, _) ins outs =
    let (callee', callee_t) =
      let c = type_check_expression env coiface [] callee in
	(c , Expression.get_type c)
    in
    let ifaces =
      try
	match callee_t with
	  | Type.Intersection l ->
	      List.map
		(fun i -> Program.find_interface env.program (Type.name i)) l
	  | Type.Internal ->
	      []
	  | Type.Application (_, [Type.Basic n])
	      when Type.collection_p callee_t ->
	      [Program.find_interface env.program n]
	  | Type.Basic n | Type.Application (n, _)->
	      [Program.find_interface env.program n]
	  | _ ->
	      assert false
      with
	  Not_found ->
	    raise (Type_error (n.file, n.line,
			       "Interface " ^ (Type.string_of_type callee_t) ^
				 " not defined."))
    and future' =
      match future with
	  None -> future
	| Some l -> Some (type_check_lhs env coiface l)
    and (ins'', ins_t'') =
      (* Observe that ins'' and ins_t may still contain parameterised types
	 and we cannot use these too look up the method we want to call. *)
      let i =
	type_check_expression_list env coiface [] ins
      in
	(i, List.map Expression.get_type i)
    in
    let (outs', outs_t) =

      (* Here we have to guess a correct output type.  If [future]
	 has been provided, then [outs_t] must be [None] and get it
	 from the future. *)
      
      match (future', outs) with
	  (None, None) -> (None, None)
	| (None, Some ol) ->
	    let o =
	      List.map (type_check_lhs env coiface) ol
	    in
	      (Some o, Some (List.map Expression.get_lhs_type o))
	| (Some l, None) ->
	    (None, Some (Type.type_of_future (Expression.get_lhs_type l)))
	| (Some _, Some _) -> assert false
    in
    let co' =

      (* Infer the co-interface.  This is either the type of the class
	 or a provided co-interface using the {i as} annotation. *)

      match asco with
	  None -> Class.get_type env.cls
	| Some c ->
	    
	    (* Make sure the provided cointerface is actually implemented
	       by the current class. *)
	    
	    if Program.subtype_p env.program (Class.get_type env.cls) c then
	      c
	    else
	      raise (Type_error (n.file, n.line, (Type.string_of_type c) ^
				   " is not implemented by class " ^
				   env.cls.Class.name ^ " of type " ^
				   (Type.string_of_type (Class.get_type env.cls))))
    in
    let (ins', ins_t') =

      (* Find the set of all possible candidate methods for the
	 inferred signature. Here we cannot assume that the types
	 inferred for the input parameters are all ground type
	 terms.  Therefore, we have to build a unification problem
	 first and resolve the types.  *)

      let cands' =
	List.fold_left
	  (fun a iface ->
	     List.fold_left (fun a' e' -> MSet.add e' a') a
	       (Program.interface_find_methods env.program iface m
		  (Some co', None, outs_t)))
	  MSet.empty ifaces
      in
      let cands_type =
	(* Build a disjunctive type from all the inputs. *)
	Type.Disjunction
	  (List.map
	     (fun m ->
		Type.Function (Method.domain_type m, Method.range_type m))
	     (MSet.elements cands'))

      and call_type =
	(* the actual call will have a parameterised type. *)
	match outs_t with
	    None -> Type.Function (Type.Tuple ins_t'', Type.Variable "__")
	  | Some t -> Type.Function (Type.Tuple ins_t'', Type.Tuple t)
      in
      let subst = 
	try
	  unify env.program [(call_type, cands_type)]
	with
	    Unify_failure (s, t) ->
	      raise (Type_error (n.file, n.line,
				 (Type.string_of_type s) ^
				   " but expected is type " ^
				   (Type.string_of_type t) ^
				   "\n  Cannot satisfy constraints: " ^
				   (string_of_constraint_set
				      [(call_type, cands_type)])))
      in
        Messages.message 2 (Type.string_of_substitution subst) ;
	let i = List.map (substitute_types_in_expression subst) ins'' in
	  (i, List.map Expression.get_type i)
    in
    let co =
      let cands =
	(* Now the type of the input parameters have been resolved.
	   We must recheck the signature of the call, because the
	   unification algorithm could have guessed something more
	   precise or a signature from the wrong co-interface.

	   TODO: Make sure this statement is actually correct. *)
	List.fold_left
	  (fun a iface ->
	     List.fold_left (fun a' e' -> MSet.add e' a') a
	       (Program.interface_find_methods env.program iface m
		  (Some co', Some ins_t', outs_t)))
	  MSet.empty ifaces
      in
	match MSet.cardinal cands with
	    0 -> raise (Type_error (n.file, n.line,
				    "Interface " ^
				      (Type.string_of_type callee_t) ^
				      " does not provide a method " ^ m ^ 
				      " with signature " ^
				      (Type.string_of_sig
					 (Some co', Some ins_t', outs_t))))
	  | 1 -> (MSet.choose cands).Method.coiface
	  | _ -> error_ambigous n m callee_t cands
    in
      if (Program.contracts_p env.program env.cls co) then
	(future', callee', (Some co, Some ins_t', outs_t), ins', outs')
      else
	raise (Type_error (n.file, n.line,
	  		   "Class " ^ env.cls.Class.name ^
			     " does not contract interface " ^
			     (Type.string_of_type co)))
  in
  let check_async_method_call n future callee m sign ins =
    let (future', callee', sign', ins', _) =
      check_method_call n future callee m sign ins None
    in
      (future', callee', sign', ins')
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
	  None -> env.cls
	| Some x ->
	    if Program.subclass_p env.program env.cls.Class.name x then
	      Program.find_class env.program x
	    else
	      raise (Type_error (n.file, n.line,
			         "Class " ^ x ^ " is not a subclass of " ^
				   env.cls.Class.name))
    in

      (* FIXME: We check for an internal method only, but in the
	 paper {e A Dynamic Binding Strategy ...} and the
	 authorisation policy example this mechanism is used to
	 access any method internally. *)

      match ub with
	  None -> 
	    if Program.class_provides_method_p env.program c' m signature then
	      ()
	    else
	      raise (Type_error (n.file, n.line,
				 "Class " ^ c'.Class.name ^
				   " does not provide method " ^ m ^
				   (Type.string_of_sig signature)))
	| Some y ->
	    let cands =
	      Program.class_find_methods env.program c' m signature
	    in
	    let p m =
	      Program.subclass_p env.program y m.Method.location
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
      type_check_expression_list env coiface [] ins
    in
    let ins_t = List.map Expression.get_type ins' in
    let signature = (Some Type.Internal, Some ins_t, outs_t) in
    let () = check_method_bounds n m signature lb ub
    in (signature, ins')
  in
  let check_local_sync_call n m lb ub ins outs =
    let (ins', ins_t) =
      let i =
	type_check_expression_list env coiface [] ins
      in
	(i, List.map Expression.get_type i)
    and (outs', outs_t) =
      let o =
	List.map (type_check_lhs env coiface) outs
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
	  let e' = type_check_assertion env coiface e in
	    Assert (n, e')
      | Prove (n, e) ->
	  let e' = type_check_assertion env coiface e in
	    Prove (n, e')
      | Assign (n, lhs, rhs) ->
	  let lhs' = List.map (type_check_lhs env coiface) lhs
	  and rhs' = type_check_expression_list env coiface [] rhs
	  in
	  let check_assignment_pair lhs rhs =
	    (* It has to be checked whether for each assignment part
	       we find a free type variable in the right-hand-side.
	       If this is the case we have to unify it with the type
	       of the left-hand-side.  On the left hand side the
	       type must not contain any free variables. *)
	    let lhs_t = Expression.get_lhs_type lhs
	    and rhs_t = Expression.get_type rhs in
	    let s =
	      try
		unify env.program [(rhs_t, lhs_t)]
	      with
		  Unify_failure _ ->
	            raise (Type_error (n.file, n.line,
			"Type mismatch in assignment: Expected " ^
			(Type.string_of_type lhs_t) ^
			" but got " ^
			(Type.string_of_type rhs_t)))

		in
                  let () = log 1 (Type.string_of_substitution s) in
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
	  let e' = type_check_assertion env coiface e in
	    Await (n, e')
      | Posit (n, e) ->
	  let e' = type_check_assertion env coiface e in
	    Posit (n, e')
      | Get (n, future, retvals) -> 
	  let future' =
	    type_check_expression env coiface [] future
	  and retvals' =
	    List.map (type_check_lhs env coiface) retvals
	  in
	    if Program.subtype_p env.program
	      (Type.Tuple (List.map get_lhs_type retvals'))
	      (Type.Tuple (Type.type_of_future (Expression.get_type future')))
	    then
	      Get (n, future', retvals')
	    else
	      raise (Type_error (n.file, n.line, "Type mismatch"))
      | Free (n, args) -> assert false
      | Bury (n, args) -> assert false
      | AsyncCall (n, future, callee, m, sign, ins) ->
	  let (future', callee', sign', ins') =
	    check_async_method_call n future callee m sign ins
	  in
	    AsyncCall (n, future', callee', m, sign', ins')
      | LocalAsyncCall (n, None, m, _, lb, ub, args) ->
	  let (signature, args') =
	    check_local_async_call n m lb ub args None
	  in
	    LocalAsyncCall (n, None, m, signature, lb, ub, args')
      | LocalAsyncCall (n, Some future, m, _, lb, ub, args) ->
	  let l' = type_check_lhs env coiface future in
	  let lt = Type.type_of_future (Expression.get_lhs_type l') in
	  let (signature, args') =
	    check_local_async_call n m lb ub args (Some lt)
	  in
	    LocalAsyncCall (n, Some l', m, signature, lb, ub, args')
      | MultiCast (n, callee, m, sign, ins) ->
	  let (future', callee', sign', ins') =
	    check_async_method_call n None callee m sign ins
	  in
	    AsyncCall (n, future', callee', m, sign', ins')
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
      | StaticTail _ -> assert false
      | Return _ -> assert false
      | If (n, cond, iftrue, iffalse) ->
	  let cond' = type_check_assertion env coiface cond in
	    If (n, cond',
		type_check_statement env coiface iftrue,
		type_check_statement env coiface iffalse)
      | While (n, cond, inv, body) ->
	  let cond' = type_check_assertion env coiface cond
	  and inv' = type_check_assertion env coiface inv
	  in
	    While (n, cond', inv',
		   type_check_statement env coiface body)
      | DoWhile (n, cond, inv, body) ->
	  let cond' = type_check_assertion env coiface cond
	  and inv' = type_check_assertion env coiface inv
	  in
	    DoWhile (n, cond', inv',
		     type_check_statement env coiface body)
      | Sequence (n, s1, s2) ->
	  let s1' = type_check_statement env coiface s1 in
	  let s2' = type_check_statement env coiface s2 in
	    Sequence (n, s1', s2')
      | Merge (n, s1, s2) ->
	  let s1' = type_check_statement env coiface s1
	  and s2' = type_check_statement env coiface s2 in
	    Merge (n, s1', s2')
      | Choice (n, s1, s2) ->
	  let s1' = type_check_statement env coiface s1
	  and s2' = type_check_statement env coiface s2 in
	    Choice (n, s1', s2')
      | Continue _ -> assert false
      | Extern _ as s -> s


(** The function [method_missing_for_interface program cls name]
    checks, whether all methods declared in the interface called
    [name] are defined by the class [cls] or one of its superclasses.
    Returns the number of missing methods. *)
let methods_missing_for_iface ~program ~cls ~name =
  let i = Program.find_interface program name in
  let report m =
    Messages.error cls.Class.file cls.Class.line
      ("Class " ^ cls.Class.name ^ " does not provide a method " ^ m ^
	 " declared in interface " ^ i.Interface.name)
  in
  let methods_missing_for_with w = 
    let p m =
      let s =
	let d =
	  match Method.domain_type m with
	      Type.Tuple x -> x
	    | _ -> assert false
	and r =
	  match Method.range_type m with 
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


(** Type check a tree. *)
let typecheck tree: Program.t =
  let rec type_check_inits env coiface res =
    function
      | [] -> res
      | ({ VarDecl.init = None } as v)::r ->
	  type_check_inits env coiface (v::res) r
      | { VarDecl.name = n; var_type = t; init = Some i }::r ->
	  let i' =
	    let l = [LhsId (Expression.make_note (), n)]
	    and r = [i]
	    and e = { env with meth = { env.meth with Method.vars = { VarDecl.name = n; var_type = t; init = None }::res } }
	    in
	    let s = type_check_statement e coiface (Assign (make_note (), l, r)) in
	      match s with
		| Assign (_, _, [i']) -> i'
		| _ -> assert false
	  in
	    type_check_inits env coiface
	      ({ VarDecl.name = n; var_type = t; init = Some i' }::res) r
  and type_check_variables env coiface meth =
    List.rev (type_check_inits env coiface [] meth.Method.vars)
  and type_check_method program cls coiface meth =
    let env = { program = program; cls = cls; meth = meth; env = Env.empty } in
    let env' = { env with meth = { meth with Method.vars = [] } }  in
    let () =
      let f d { VarDecl.name = n; var_type = t } =
	if not (Program.type_p program t) then
	  raise (Type_error (cls.Class.file, cls.Class.line,
			     "type " ^ (Type.string_of_type t) ^ " of " ^ d ^
			       " parameter " ^ n ^ " does not exist"))
      in
	List.iter (f "input") meth.Method.inpars ;
	List.iter (f "output") meth.Method.outpars
    in
    let r' = type_check_assertion env' coiface meth.Method.requires
    and e' = type_check_assertion env' coiface meth.Method.ensures
    and v' = type_check_variables env' coiface meth
    and b' = match meth.Method.body with
	None -> None
      | Some s -> Some (type_check_statement env coiface s)
    in
      { meth with Method.requires = r'; ensures = e'; vars = v' ; body = b' }
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
      let env =
	{ program = program; cls = cls; meth = Method.empty; env = Env.empty }
      in
	List.map (type_check_assertion env coiface) w.With.invariants
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
	match i with
	  | None -> 
	      { VarDecl.name = n; var_type = t; init = i }
	  | Some init ->
	      let i' =
		let l = [LhsId (Expression.make_note (), n)]
		and r = [init]
		and env =
		  { program = program; cls = cls; meth = Method.empty;
		    env = Env.empty }
		in
		let s =
		  type_check_statement env "Any" (Assign (make_note (), l, r))
		in
		  match s with
		    | Assign (_, _, [i']) -> i'
		    | _ -> assert false
	      in
		{ VarDecl.name = n; var_type = t; init = Some i' }
      else
	raise (Type_error (cls.Class.file, cls.Class.line,
			   "type " ^
			     (Type.string_of_type t) ^ " of attribute " ^ n ^
			     " does not exist"))

    and parameter_well_typed { VarDecl.name = n; var_type = t } =
      if Program.type_p program t then
	true
      else
	begin
	  Messages.error cls.Class.file cls.Class.line
	    ("type " ^ (Type.string_of_type t) ^ " of class parameter " ^ n ^
	       " does not exist") ;
	  false
	end
    in
      try
	ignore (Program.superclasses program cls.Class.name) ;
	let () =
	  if (List.fold_left
		(fun a v -> if parameter_well_typed v then a else a + 1)
		0 cls.Class.parameters) > 0 then
	    exit 1
	in
	let attributes' =
	  List.map attribute_well_typed cls.Class.attributes
	in
	  begin
	    let methods_missing =
	      let count n =
		try
		  methods_missing_for_iface program cls n
		with
		    Not_found ->
		      Messages.error cls.Class.file cls.Class.line
			("No interface " ^ n ^ " defined") ;
		      1
	      in
		try
		  IdSet.fold (fun n a -> a + (count n))
                    (Program.class_provides program cls) 0
		with
	            Program.Interface_not_found (file, line, iface) ->
		      Messages.error file line ("Interface " ^ iface ^
						  " not found") ;
		      1
	    in
	      if (methods_missing = 0) then
		{ cls with Class.attributes = attributes';
		    with_defs = List.map (type_check_with_def program cls)
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
  and type_relation_well_formed_p tree =
    let rel = Program.subtype_relation tree in
      if Program.acyclic_p (Program.transitive_closure rel) then
	true
      else
	begin
	  let cycle = Program.find_cycle rel in
	    Messages.error "*top*" 0 ("subtype relation has a cycle: " ^
					(Program.string_of_cycle cycle)) ;
	    false
	end
  and class_hierarchy_well_formed_p tree =
    let rel = Program.class_hierarchy tree in
      if Program.acyclic_p (Program.transitive_closure rel) then
	true
      else
	begin
	  let cycle = Program.find_cycle rel in
	    Messages.error "*top*" 0 ("class hierarchy has a cycle: " ^
					(Program.string_of_cycle cycle)) ;
	    false
	end
  in
    if (type_relation_well_formed_p tree) &&
      (class_hierarchy_well_formed_p tree)
    then
      begin
	try
	  Program.map tree (type_check_declaration tree)
	with
	    Type_error (file, line, msg) ->
	      Messages.error file line msg ;
	      exit 1
      end
    else
      exit 1
