(*
 * CreolTyping.ml -- Type analysis for Creol.
 *
 * This file is part of creolcomp
 *
 * Written and Copyright (c) 2007
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

open Creol
open Expression
open Statement

exception TypeError of string * int * string


let typecheck tree: Declaration.t list =
  let cnt = ref 0 in
  let fresh_name () = let _ = incr cnt in "_" ^ (string_of_int !cnt) in
  let ambigous_msg thing name arg_t cands =
    let cand_s { Operation.name = n; parameters = p; result_type = r } =
      let oper_t =
	Type.Function (List.map (fun v -> v.VarDecl.var_type) p, r)
      in
	name ^ (Type.as_string oper_t)
    in
      thing ^ " " ^ name ^ (Type.as_string arg_t) ^
	" ambigous.\nPossible candidates are:\n" ^
	(List.fold_left (fun c o -> c ^ "    " ^ (cand_s o) ^ "\n") "" cands)
  in
  let rec type_check_expression program cls meth coiface =
    function
	This n ->
	  This (set_type n (Class.get_type cls))
      | Caller n ->
	  Caller (set_type n (Type.Basic coiface))
      | Null n ->
	  Null (set_type n (Type.Variable (fresh_name ())))
      | Nil n ->
	  Nil (set_type n (Type.Application ("List", [(Type.Variable (fresh_name ()))])))
      | Now n ->
	  Now (set_type n (Type.Basic "Time"))
      | Bool (n, value) ->
	  Bool (set_type n (Type.Basic "Bool"), value)
      | Int (n, value) ->
	  Int (set_type n (Type.Basic "Int"), value)
      | Float (n, value) ->
	  Float (set_type n (Type.Basic "Float"), value)
      | String (n, value) ->
	  String (set_type n (Type.Basic "String"), value)
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
			raise (TypeError ((Expression.file n),
					 (Expression.line n),
					 "Identifier " ^ name ^
					   " not declared"))
	  in
	    Id (set_type n res, name)
      | StaticAttr (n, name, (Type.Basic c)) ->
	  (* FIXME: Here we should also check whether cls is the
	     current class name or inherited by the current class. *)
	  let res =
	    Program.find_attr_decl program (Program.find_class program c) name
	  in
	    StaticAttr (set_type n res.VarDecl.var_type, name, (Type.Basic c))
      | StaticAttr _ -> assert false
      | Unary (n, op, arg) ->
	  let narg =
	    type_check_expression program cls meth coiface arg
	  in
	  let narg_t = List.map get_type [narg] in
	  let restype =
	    match Program.find_functions program (string_of_unaryop op) narg_t
	    with
		[] ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Unary operator " ^
				     (string_of_unaryop op) ^
				     " not defined"))
	      | [oper] -> oper.Operation.result_type
	      | candidates ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   ambigous_msg "Unary operator "
				     (string_of_unaryop op)
				     (Type.Tuple narg_t)
				     candidates))
	  in
	    Unary (set_type n restype, op, narg)
      | Binary (n, op, arg1, arg2) ->
	  let narg1 =
	    type_check_expression program cls meth coiface arg1
	  and narg2 =
	    type_check_expression program cls meth coiface arg2
	  in
	  let oper_n = string_of_binaryop op 
	  and nargs_t = List.map get_type [narg1; narg2] in
	  let restype =
	    match Program.find_functions program oper_n nargs_t with
		[] ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Binary operator " ^
				     (string_of_binaryop op) ^
				     (Type.as_string (Type.Tuple nargs_t)) ^
				     " not defined"))
	      | [oper] -> oper.Operation.result_type
	      | candidates ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   ambigous_msg "Binary operator "
				     (string_of_binaryop op)
				     (Type.Tuple nargs_t)
				     candidates))
	  in
	    Binary (set_type n restype, op, narg1, narg2)
      | Expression.If (n, cond, iftrue, iffalse) ->
	  let ncond =
	    type_check_expression program cls meth coiface cond
	  and niftrue =
	    type_check_expression program cls meth coiface iftrue
	  and niffalse =
	    type_check_expression program cls meth coiface iffalse
	  in
	    if (Expression.get_type ncond) = Type.boolean then
	      let restype =
		Program.meet program [get_type niftrue; get_type niffalse]
	      in
		Expression.If (set_type n restype, ncond, niftrue, niffalse)
	    else
	      raise (TypeError (Expression.file n, Expression.line n,
			       "Condition must be boolean"))
      | FuncCall (n, name, args) ->
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  in
	  let nargs_t = List.map get_type nargs in
	  let restype =
	    match (Program.find_functions program name nargs_t) with
		[] -> raise (TypeError (Expression.file n, Expression.line n,
				       "Function " ^ name ^ " not defined"))
	      | [oper] -> oper.Operation.result_type
	      | candidates ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   ambigous_msg "Function"
				     name
				     (Type.Tuple nargs_t)
				     candidates))
	  in
	    FuncCall (set_type n restype, name, nargs)
      | Label (n, (Id (_, name) | SSAId(_, name, _) as l)) ->
	  let exists =
	    try
	      match Method.find_variable meth name with _ -> true
	    with
		Not_found -> false
	  in
	    if exists then
	      Label (set_type n (Type.Basic "Bool"), l)
	    else
	      raise (TypeError (Expression.file n, Expression.line n,
			       "Label " ^ name ^ " not declared"))
      | New (n, Type.Basic c, args) ->
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  in
          let args_t = Type.Tuple (List.map get_type nargs) in
	  let cls_n =
	    try
	      Program.find_class program c
	    with
		Not_found ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Class " ^ c ^ " not defined"))
	  in
	  let ctor_t = Type.Tuple
	    (List.map (fun x -> x.VarDecl.var_type)
		cls_n.Class.parameters)
	  in
	    if
	      Program.subtype_p program Program.empty args_t ctor_t
	    then
	      New (set_type n (Class.get_type (Program.find_class program c)),
		  Type.Basic c, nargs)
	    else
	      raise (TypeError (Expression.file n, Expression.line n,
			       "Arguments to new " ^ c ^
				 " mismatch: expected " ^
				 (Type.as_string ctor_t) ^ " but got " ^
				 (Type.as_string args_t)))

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
			raise (TypeError ((Expression.file n),
					 (Expression.line n),
					 "Identifier " ^ name ^
					   " not declared"))
	  in
	    SSAId (set_type n res, name, version)
      | Phi (n, args) ->
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  in
	  let nty =
	    Program.meet program (List.map get_type nargs)
	  in
	    Phi (set_type n nty, nargs)
  and type_check_lhs program (cls: Class.t) meth coiface =
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
			raise (TypeError ((Expression.file n),
					 (Expression.line n),
					 "Identifier " ^ name ^
					   " not declared"))
	  in
	    LhsVar (set_type n res, name)
      | LhsAttr (n, name, (Type.Basic c)) ->
	  let res =
	    (Program.find_attr_decl program (Program.find_class program c) name).VarDecl.var_type
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
			raise (TypeError ((Expression.file n),
					 (Expression.line n),
					 "Identifier " ^ name ^
					   " not declared"))
	  in
	    LhsSSAId (set_type n res, name, version)
  and type_check_statement program cls meth coiface =
    function
	Skip n -> Skip n
      | Release n -> Release n
      | Assert (n, e) ->
	  Assert (n, type_check_expression program cls meth coiface e)
      | Assign (n, lhs, rhs) ->
	  let nlhs =
	    List.map (type_check_lhs program cls meth coiface) lhs
	  and nrhs =
	    List.map (type_check_expression program cls meth coiface) rhs
	  in
	  let lhs_t = Type.Tuple (List.map Expression.get_lhs_type nlhs)
	  and rhs_t = Type.Tuple (List.map Expression.get_type nrhs)
	  in
	    if Program.subtype_p program Program.empty rhs_t lhs_t
	    then
	      Assign (n, nlhs, nrhs)
	    else
	      raise (TypeError (file n, line n,
			       "Type mismatch in assignment: Expected " ^
				 (Type.as_string lhs_t) ^ " but got " ^
				 (Type.as_string rhs_t)))
      | Await (n, e) ->
	  Await (n, type_check_expression program cls meth coiface e)
      | Posit (n, e) ->
	  Posit (n, type_check_expression program cls meth coiface e)
      | AsyncCall (n, None, callee, m, _, args) ->
	  let ncallee =
	    type_check_expression program cls meth coiface callee
	  and nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  in
	  let callee_t = (Expression.get_type ncallee) in
	  let co =
	    Interface.cointerface (Program.find_interface program 
				      (Type.as_string callee_t))
	  in
	  let signature =
	    (co, Type.Tuple (List.map Expression.get_type nargs), Type.data)
	  in
	    if (Class.contracts_p cls co) &&
	      (Program.interface_provides_p program
		  (Program.find_interface program
		      (Type.as_string (Expression.get_type ncallee)))
		  m co (List.map Expression.get_type nargs)
		  [Type.data])
	    then
	      (* A label value of none implies that the type if that
		 anonymous label is Label[Data]. *)
	      AsyncCall (n, None, ncallee, m, signature, nargs)
	    else
	      begin
		if not (Class.contracts_p cls co) then
		  raise (TypeError (file n, line n,
				   "Class " ^ cls.Class.name ^
				     " does not contract interface " ^
				     (Type.as_string co)))
		else
		  raise (TypeError (file n, line n,
				   "Interface " ^ (Type.as_string callee_t) ^
				     " does not provide method " ^ m))
	      end
      | AsyncCall (n, Some label, callee, m, _, args) ->
	  let ncallee =
	    type_check_expression program cls meth coiface callee
	  and nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  and nlabel =
	    type_check_lhs program cls meth coiface label
	  in
	  let callee_t = (Expression.get_type ncallee) in
	  let co =
	    let iface =
	      try
	        Program.find_interface program (Type.as_string callee_t)
	      with
	          Not_found ->
		    raise (TypeError (file n, line n,
				     "Callee's interface " ^ (Type.as_string callee_t) ^
				       " not defined"))
	    in
	      try
	        Interface.cointerface iface
	      with
		  Failure _ ->
		    raise (TypeError (file n, line n,
				     "Method " ^ m ^
				       " not provided in empty interface " ^
				       iface.Interface.name))
	  in
	  let signature =
	    (co, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple
		(Type.get_from_label (Expression.get_lhs_type nlabel))))
	  in
	    if (Class.contracts_p cls co) &&
	      (Program.interface_provides_p program
		  (Program.find_interface program
		      (Type.as_string callee_t))
		  m co
		  (List.map get_type nargs)
		  (Type.get_from_label (Expression.get_lhs_type nlabel)))
	    then
	      AsyncCall (n, Some nlabel, ncallee, m, signature, nargs)
	    else
	      begin
		if not (Class.contracts_p cls co) then
		  raise (TypeError (file n, line n,
				   "Class " ^ cls.Class.name ^
				     " does not contract interface " ^
				     (Type.as_string co)))
		else
		  raise (TypeError (file n, line n,
				   "Interface " ^ (Type.as_string callee_t) ^
				     " does not provide method " ^ m))
	      end
      | Reply (n, label, retvals) -> 
	  let nlabel =
	    type_check_expression program cls meth coiface label
	  and nretvals =
	    List.map (type_check_lhs program cls meth coiface) retvals
	  in
	    if Program.subtype_p program Program.empty
	      (Type.Tuple (List.map get_lhs_type nretvals))
	      (Type.Tuple (Type.get_from_label (Expression.get_type nlabel)))
	    then
	      Reply (n, nlabel, nretvals)
	    else
	      raise (TypeError (file n, line n, "Type mismatch"))
      | Free (n, args) -> assert false
      | LocalAsyncCall (n, None, m, _, lb, ub, args) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
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
	      raise (TypeError (file n, line n,
			       "Class " ^ cls.Class.name ^
				 " does not provide method " ^ m))
      | LocalAsyncCall (n, Some label, m, _, lb, ub, args) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  and nlabel =
	    type_check_lhs program cls meth coiface label
	  in
	  let signature =
	    (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple
		(Type.get_from_label (Expression.get_lhs_type nlabel))))
	  in
	    if Program.class_provides_method_p program cls m
	      (Type.Tuple (List.map get_type nargs))
	      (Type.Tuple
		  (Type.get_from_label (Expression.get_lhs_type nlabel)))
	    then
	      LocalAsyncCall (n, Some nlabel, m, signature, lb, ub, nargs)
	    else
	      raise (TypeError (file n, line n,
			       "Class " ^ cls.Class.name ^
				 " does not provide method " ^ m))
      | SyncCall (n, callee, m, _, args, retvals) ->
	  let ncallee =
	    type_check_expression program cls meth coiface callee
	  and nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  and nouts =
	    List.map (type_check_lhs program cls meth coiface) retvals
	  in
	  let callee_t = (Expression.get_type ncallee) in
	  let co =
	    let iface =
	      try
		Program.find_interface program (Type.as_string callee_t)
	      with
		  Not_found -> 
		    raise (TypeError (file n, line n,
				     "Callee's interface " ^ (Type.as_string callee_t) ^
				       " not defined"))
	    in
	      try
	        Interface.cointerface iface
	      with
		  Failure _ ->
		    raise (TypeError (file n, line n,
				     "Method " ^ m ^
				       " not provided in empty interface " ^
				       iface.Interface.name))
	  in
	  let signature =
	    (co, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple (List.map Expression.get_lhs_type nouts)))
	      
	  in
	    if (Class.contracts_p cls co) &&
	      (Program.interface_provides_p program
		  (Program.find_interface program
		      (Type.as_string callee_t))
		  m
		  co
		  (List.map get_type nargs)
		  (List.map get_lhs_type nouts))
	    then
	      SyncCall (n, ncallee, m, signature, nargs, nouts)
	    else
	      begin
		if not (Class.contracts_p cls co) then
		  raise (TypeError (file n, line n,
				   "Class " ^ cls.Class.name ^
				     " does not contract interface " ^
				     (Type.as_string co)))
		else
		  raise (TypeError (file n, line n,
				   "Interface " ^ (Type.as_string callee_t) ^
				     " does not provide method " ^ m))
	      end
      | AwaitSyncCall (n, callee, m, _, args, retvals) ->
	  let ncallee =
	    type_check_expression program cls meth coiface callee
	  and nargs =
	    List.map (type_check_expression program cls meth coiface)
	      args
	  and nouts =
	    List.map (type_check_lhs program cls meth coiface) retvals
	  in
	  let callee_t = Expression.get_type ncallee in
	  let co =
	    Interface.cointerface (Program.find_interface program
				      (Type.as_string callee_t))
	  in
	  let signature =
	    (co, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple (List.map Expression.get_lhs_type nouts)))
	      
	  in
	    if (Class.contracts_p cls co) &&
	      (Program.interface_provides_p program
		  (Program.find_interface program
		      (Type.as_string callee_t))
		  m
		  co
		  (List.map get_type nargs)
		  (List.map get_lhs_type nouts))
	    then
	      AwaitSyncCall (n, ncallee, m, signature, nargs, nouts)
	    else
	      begin
		if not (Class.contracts_p cls co) then
		  raise (TypeError (file n, line n,
				   "Class " ^ cls.Class.name ^
				     " does not contract interface " ^
				     (Type.as_string co)))
		else
		  raise (TypeError (file n, line n,
				   "Interface " ^ (Type.as_string callee_t) ^
				     " does not provide method " ^ m))
	      end	  
      | LocalSyncCall (n, m, _, lb, ub, args, retvals) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
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
	      raise (TypeError (file n, line n,
			       "Class " ^ cls.Class.name ^
				 " does not provide method " ^ m))
      | AwaitLocalSyncCall (n, m, _, lb, ub, args, retvals) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls meth coiface)
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
	      raise (TypeError (file n, line n,
			       "Class " ^ cls.Class.name ^
				 " does not provide method " ^ m))
      | Tailcall _ -> assert false
      | If (n, cond, iftrue, iffalse) ->
	  If (n, type_check_expression program cls meth coiface cond,
	     type_check_statement program cls meth coiface iftrue,
	     type_check_statement program cls meth coiface iffalse)
      | While (n, cond, None, body) ->
	  While (n, type_check_expression program cls meth coiface cond,
		None,
		type_check_statement program cls meth coiface body)
      | While (n, cond, Some inv, body) ->
	  While (n, type_check_expression program cls meth coiface cond,
		Some (type_check_expression program cls meth coiface inv),
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
    { meth with Method.meth_body =
	match meth.Method.meth_body with
	    None -> None
	  | Some s ->
	      Some (type_check_statement program cls meth coiface s) }
  and type_check_with_def program cls w =
    let coiface =
      match w.With.co_interface with
	  None -> ""
	| Some c -> c
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
    List.map (type_check_declaration tree) tree
