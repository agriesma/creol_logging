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
  let rec type_check_expression program cls gamma delta coiface =
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
	      Hashtbl.find delta name 
	    with
		Not_found ->
		  try
		    Hashtbl.find gamma name
		  with
		      Not_found ->
			raise (TypeError ((Expression.file n),
					 (Expression.line n),
					 "Identifier " ^ name ^
					 " not declared"))
	  in
	    Id (set_type n res, name)
      | StaticAttr (n, name, cls) ->
	  (* FIXME: Here we should also check whether cls is the
	     current class name or inherited by the current class. *)
	  let res = Program.find_attr_decl program cls name in
	    StaticAttr (set_type n res.VarDecl.var_type, name, cls)
      | Unary (n, op, arg) ->
	  let narg =
	    type_check_expression program cls gamma delta coiface arg
	  in
	  let restype =
	    try
	      (Program.find_function program (string_of_unaryop op)
		  (List.map get_type [narg])).Operation.result_type
	    with
		Program.Function_not_found [] ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Unary operator " ^
				     (string_of_unaryop op) ^
				     " not defined"))
	      | Program.Function_not_found l ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Unary operator " ^
				     (string_of_unaryop op) ^
				     " ambigous"))
	  in
	    Unary (set_type n restype, op, narg)
      | Binary (n, op, arg1, arg2) ->
	  let narg1 =
	    type_check_expression program cls gamma delta coiface arg1
	  and narg2 =
	    type_check_expression program cls gamma delta coiface arg2
	  in
	  let restype =
	    try
	      (Program.find_function program (string_of_binaryop op)
		  (List.map get_type [narg1; narg2])).Operation.result_type
	    with
		Program.Function_not_found [] ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Binary operator " ^
				     (string_of_binaryop op) ^
				     " not defined"))
	      | Program.Function_not_found l ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Binary operator " ^
				     (string_of_binaryop op) ^
				     " ambigous"))
	  in
	    Binary (set_type n restype, op, narg1, narg2)
      | Expression.If (n, cond, iftrue, iffalse) ->
	  let ncond =
	    type_check_expression program cls gamma delta coiface cond
	  and niftrue =
	    type_check_expression program cls gamma delta coiface iftrue
	  and niffalse =
	    type_check_expression program cls gamma delta coiface iffalse
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
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  in
	  let nargs_t = List.map get_type nargs in
	  let restype =
	    try
	      (Program.find_function program name
		  nargs_t).Operation.result_type
	    with
		Program.Function_not_found [] ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Function " ^ name ^
				     (Type.as_string (Type.Tuple nargs_t)) ^
				     " not defined"))
	      | Program.Function_not_found l ->
		  raise (TypeError (Expression.file n, Expression.line n,
				   "Function " ^ name ^
				     (Type.as_string (Type.Tuple nargs_t)) ^
				     " ambigous"))
	  in
	    FuncCall (set_type n restype, name, nargs)
      | Label (n, (Id (_, name) | SSAId(_, name, _) as l)) ->
	  if Hashtbl.mem delta name then
	    Label (set_type n (Type.Basic "Bool"), l)
	  else
	    raise (TypeError (Expression.file n, Expression.line n,
			     "Label " ^ name ^ " not declared"))
      | New (n, Type.Basic c, args) ->
	  let nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  in
          let args_t = Type.Tuple (List.map get_type nargs) in
	  let ctor_t = Type.Tuple
		    (List.map (fun x -> x.VarDecl.var_type)
			(Program.find_class program c).Class.parameters)
	  in
	    if
	      Program.subtype_p program args_t ctor_t
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
	      Hashtbl.find delta name 
	    with
		Not_found ->
		  try
		    Hashtbl.find gamma name
		  with
		      Not_found ->
			raise (TypeError (Expression.file n, Expression.line n,
					 "Identifier " ^ name ^
					 " not declared"))
	  in
	    SSAId (set_type n res, name, version)
      | Phi (n, args) ->
	  let nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  in
	  let nty =
	    Program.meet program (List.map get_type nargs)
	  in
	    Phi (set_type n nty, nargs)
  and type_check_lhs program cls gamma delta coiface =
    function
	LhsVar (n, name) ->
	  let res =
	    try
	      Hashtbl.find delta name 
	    with
		Not_found ->
		  try
		    Hashtbl.find gamma name
		  with
		      Not_found ->
			raise (TypeError (Expression.file n, Expression.line n,
					 name ^ " not declared"))
	  in
	    LhsVar (set_type n res, name)
      | LhsAttr (n, name, ty) ->
	  let res = (Program.find_attr_decl program cls name).VarDecl.var_type
	  in
	    LhsAttr (set_type n res, name, cls)
      | LhsWildcard (n, None) ->
	  LhsWildcard(set_type n Type.data, None)
      | LhsWildcard (n, Some ty) ->
	  LhsWildcard(set_type n ty, Some ty)
      | LhsSSAId (n, name, version) ->
	  let res =
	    try
	      Hashtbl.find delta name 
	    with
		Not_found ->
		  try
		    Hashtbl.find gamma name
		  with
		      Not_found ->
			raise (TypeError (Expression.file n, Expression.line n,
					 name ^ " not declared"))
	  in
	    LhsSSAId (set_type n res, name, version)
  and type_check_statement program cls gamma delta coiface =
    function
	Skip n -> Skip n
      | Release n -> Release n
      | Assert (n, e) ->
	  Assert (n, type_check_expression program cls gamma delta coiface e)
      | Assign (n, lhs, rhs) ->
	  let nlhs =
	    List.map (type_check_lhs program (Type.Basic cls.Class.name) gamma delta coiface) lhs
	  and nrhs =
	    List.map (type_check_expression program cls gamma delta coiface) rhs
	  in
	  let lhs_t = Type.Tuple (List.map Expression.get_lhs_type nlhs)
	  and rhs_t = Type.Tuple (List.map Expression.get_type nrhs)
	  in
	    if Program.subtype_p program rhs_t lhs_t
	    then
	      Assign (n, nlhs, nrhs)
	    else
	      raise (TypeError (file n, line n,
			       "Type mismatch in assignment: Expected " ^
			       (Type.as_string lhs_t) ^ " but got " ^
			       (Type.as_string rhs_t)))
      | Await (n, e) ->
	  Await (n, type_check_expression program cls gamma delta coiface e)
      | Posit (n, e) ->
	  Posit (n, type_check_expression program cls gamma delta coiface e)
      | AsyncCall (n, None, callee, meth, _, args) ->
	  let ncallee =
	    type_check_expression program cls gamma delta coiface callee
	  and nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
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
		  meth co (List.map Expression.get_type nargs)
		  [Type.data])
	    then
	      (* A label value of none implies that the type if that
		 anonymous label is Label[Data]. *)
	      AsyncCall (n, None, ncallee, meth, signature, nargs)
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
				     " does not provide method " ^ meth))
	      end
      | AsyncCall (n, Some label, callee, meth, _, args) ->
	  let ncallee =
	    type_check_expression program cls gamma delta coiface callee
	  and nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  and nlabel =
	    type_check_lhs program (Type.Basic cls.Class.name) gamma delta
	      coiface label
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
				   "Method " ^ meth ^
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
		  meth co
		  (List.map get_type nargs)
		  (Type.get_from_label (Expression.get_lhs_type nlabel)))
	    then
	      AsyncCall (n, Some nlabel, ncallee, meth, signature, nargs)
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
				     " does not provide method " ^ meth))
	      end
      | Reply (n, label, retvals) -> 
	  let nlabel =
	    type_check_expression program cls gamma delta coiface label
	  and nretvals =
	    List.map (type_check_lhs program (Type.Basic cls.Class.name) gamma
			 delta coiface) retvals
	  in
	    if Program.subtype_p program
	      (Type.Tuple (List.map get_lhs_type nretvals))
	      (Type.Tuple (Type.get_from_label (Expression.get_type nlabel)))
	    then
	      Reply (n, nlabel, nretvals)
	    else
	      raise (TypeError (file n, line n, "Type mismatch"))
      | Free (n, args) -> assert false
      | LocalAsyncCall (n, None, meth, _, lb, ub, args) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  in
	  let signature =
	    (Type.Internal,
	    Type.Tuple (List.map Expression.get_type nargs), Type.data)
	  in
	    (* A label value of none implies that the type if that
	       anonymous label is Label[Data]. *)
	    if Program.class_provides_method_p program cls meth
	      (Type.Tuple (List.map get_type nargs)) Type.data
	    then
	      LocalAsyncCall (n, None, meth, signature, lb, ub, nargs)
	    else
	      raise (TypeError (file n, line n,
			       "Class " ^ cls.Class.name ^
				 " does not provide method " ^ meth))
      | LocalAsyncCall (n, Some label, meth, _, lb, ub, args) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  and nlabel =
	    type_check_lhs program (Type.Basic cls.Class.name) gamma delta
	      coiface label
	  in
	  let signature =
	    (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple
		(Type.get_from_label (Expression.get_lhs_type nlabel))))
	  in
	    if Program.class_provides_method_p program cls meth
	      (Type.Tuple (List.map get_type nargs))
	      (Type.Tuple
		  (Type.get_from_label (Expression.get_lhs_type nlabel)))
	    then
	      LocalAsyncCall (n, Some nlabel, meth, signature, lb, ub, nargs)
	    else
	      raise (TypeError (file n, line n,
			       "Class does not provide method " ^ meth))
      | SyncCall (n, callee, meth, _, args, retvals) ->
	  let ncallee =
	    type_check_expression program cls gamma delta coiface callee
	  and nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  and nouts =
	    List.map (type_check_lhs program (Type.Basic cls.Class.name) gamma
			 delta coiface) retvals
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
				   "Method " ^ meth ^
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
		  meth
		  co
		  (List.map get_type nargs)
		  (List.map get_lhs_type nouts))
	    then
	      SyncCall (n, ncallee, meth, signature, nargs, nouts)
	    else
	      begin
		if not (Class.contracts_p cls co) then
		  raise (TypeError (file n, line n,
				   "Class does not contract interface " ^
				     (Type.as_string co)))
		else
		  raise (TypeError (file n, line n,
				   "Interface " ^ (Type.as_string callee_t) ^
				     " does not provide method " ^ meth))
	      end
      | AwaitSyncCall (n, callee, meth, _, args, retvals) ->
	  let ncallee =
	    type_check_expression program cls gamma delta coiface callee
	  and nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  and nouts =
	    List.map (type_check_lhs program (Type.Basic cls.Class.name) gamma
			 delta coiface) retvals
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
		  meth
		  co
		  (List.map get_type nargs)
		  (List.map get_lhs_type nouts))
	    then
	      AwaitSyncCall (n, ncallee, meth, signature, nargs, nouts)
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
				     " does not provide method " ^ meth))
	      end	  
      | LocalSyncCall (n, meth, _, lb, ub, args, retvals) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  and nouts =
	    List.map (type_check_lhs program (Type.Basic cls.Class.name) gamma
			 delta coiface) retvals
	  in
	  let signature =
	    (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple (List.map Expression.get_lhs_type nouts)))
		
	  in
	    if
	      Program.class_provides_method_p program cls meth
		(Type.Tuple (List.map get_type nargs))
		(Type.Tuple (List.map get_lhs_type nouts))
	    then
	      LocalSyncCall (n, meth, signature, lb, ub, nargs, nouts)
	    else
	      raise (TypeError (file n, line n,
			       "Class does not provide method " ^ meth))
      | AwaitLocalSyncCall (n, meth, _, lb, ub, args, retvals) ->
	  (* FIXME:  Check the upper bound and lower bound constraints
	     for static resolution *)
	  let nargs =
	    List.map (type_check_expression program cls gamma delta coiface)
	      args
	  and nouts =
	    List.map (type_check_lhs program (Type.Basic cls.Class.name) gamma
			 delta coiface) retvals
	  in
	  let signature =
	    (Type.Internal, Type.Tuple (List.map Expression.get_type nargs),
	    (Type.Tuple (List.map Expression.get_lhs_type nouts)))
		
	  in
	    if
	      Program.class_provides_method_p program cls meth
		(Type.Tuple (List.map get_type nargs))
		(Type.Tuple (List.map get_lhs_type nouts))
	    then
	      AwaitLocalSyncCall (n, meth, signature, lb, ub, nargs, nouts)
	    else
	      raise (TypeError (file n, line n,
			       "Class does not provide method " ^ meth))
      | Tailcall _ -> assert false
      | If (n, cond, iftrue, iffalse) ->
	  If (n, type_check_expression program cls gamma delta coiface cond,
	     type_check_statement program cls gamma delta coiface iftrue,
	     type_check_statement program cls gamma delta coiface iffalse)
      | While (n, cond, None, body) ->
	  While (n, type_check_expression program cls gamma delta coiface cond,
		None,
		type_check_statement program cls gamma delta coiface body)
      | While (n, cond, Some inv, body) ->
	  While (n, type_check_expression program cls gamma delta coiface cond,
		Some (type_check_expression program cls gamma delta coiface inv),
		type_check_statement program cls gamma delta coiface body)
      | Sequence (n, s1, s2) ->
	  let ns1 = type_check_statement program cls gamma delta coiface s1 in
	  let ns2 = type_check_statement program cls gamma delta coiface s2 in
	    Sequence (n, ns1, ns2)
      | Merge (n, s1, s2) ->
	  Merge (n, type_check_statement program cls gamma delta coiface s1,
		type_check_statement program cls gamma delta coiface s2)
      | Choice (n, s1, s2) ->
	  Choice (n, type_check_statement program cls gamma delta coiface s1,
		 type_check_statement program cls gamma delta coiface s2)
      | Extern _ as s -> s
  and insert gamma vardecl =
    begin
      if not (Hashtbl.mem gamma vardecl.VarDecl.name)
      then
	(Hashtbl.add gamma vardecl.VarDecl.name vardecl.VarDecl.var_type)
      else
	raise (TypeError ("", 0,
			 "Variable " ^ vardecl.VarDecl.name ^ " redeclared"))
    end ;
    gamma
  and type_check_method program cls gamma coiface m =
	  let d0 = Hashtbl.create 32 in
	  let d1 = List.fold_left insert d0 m.Method.meth_inpars in
	  let d2 = List.fold_left insert d1 m.Method.meth_outpars in
	  let delta = List.fold_left insert d2 m.Method.meth_vars in
	    { m with Method.meth_body =
		match m.Method.meth_body with
		    None -> None
		  | Some s ->
		      Some (type_check_statement program cls gamma delta coiface s) }
  and type_check_with_def program cls gamma w =
    let coiface =
      match w.With.co_interface with
	  None -> ""
	| Some c -> c
    in
      { w with With.methods =
	  List.map
	    (fun m -> type_check_method program cls gamma coiface m)
	    w.With.methods }
  and type_check_class program cls =
    (* Compute the type environment within a class by adding first the class
       parameters to an empty hash table and then all attributes. *)
    let g1 = List.fold_left insert (Hashtbl.create 32) cls.Class.parameters in
    let gamma = List.fold_left insert g1 cls.Class.attributes in
      { cls with Class.with_defs =
	  List.map (type_check_with_def program cls gamma) cls.Class.with_defs }
  and type_check_declaration program =
    function
	Declaration.Class c -> Declaration.Class (type_check_class program c)
      | _ as d -> d
  in
    List.map (type_check_declaration tree) tree
