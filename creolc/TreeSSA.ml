(*
 * TreeSSA.ml -- Convert a tree into or out of SSA form
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
 *)

open Creol
open Expression
open Statement

(** The information we want to collect about variables during analysis *)

type kind = Attribute | Input | Output | Local | Label

type info = {
  kind : kind ;
  version: int ;
}

let into_ssa tree =
  (** Convert a creol tree into static single assignment form.

      Static single assignment form is a form that encodes dataflow
      information syntactically.

      The algorithm used follows Marc M. Brandis and Hanspeter
      Mössenböck {i Single-Pass Generation of Static Single Assignment
      Foerm for Structured Languages}, ACM Transactions on Programming
      Languages and Systems 16(6), November 1994, p. 1684--1698.

      In contrast to the cited version, our SSA transformation does not
      compute a control-flow graph (may be later versions do).  This
      does not matter for most cases, but this algorithm must duplicate
      Phi-nodes for while statements.  See below on how this is done.

      This version is much simpler, since we only need to cover if
      statements and while loops and we do not compute dominators, and
      we operate on tree-level.  This function also treats choice
      statements.

      {b BUG}: We need to find out how we can come up with a clever
      implementation for merge statements.  We may need to expand the
      merge statements into choice statements.  For now, we assume
      that there is {i no} assignment to local variables within merge
      statements, if they are also used within the merge
      statement.

      The current code breaks on this:

      begin x := a; release; a := x end |||
      begin a := x; release; x:= a end

      This will result in

      begin x1 := a0; release; a1 := x1 end |||
      begin a2 := x0; release; x2 := a2 end

      But we are missing some phi nodes here, since the interleaving
      would make something like x1 := phi(a0, a2) and a2 := phi(x0,
      x1), a1 := phi(x1, x2), and x2 := phi(a0, a2).  How we can come
      up with something like this, and have some of these statements
      become join nodes has to be worked out.  *)
  let rec expression_to_ssa env =
    (* A use of the SSA name.  We should be able to find the name in
       the environment. *)
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
         Bool _ | Int _ | Float _ | String _ | History _) as e -> e
      | Id (a, v) ->
	  begin
	    try
	      let info = Hashtbl.find env v in
		match info.kind with
	            Attribute -> Id (a, v)
		      (* FIXME: Get the actual class of the attribute
			 from the type checker and replace it by a
			 static attribute access. *)
	          | (Input | Output) -> SSAId (a, v, info.version)
		      (* Input and output variables should be used linearily,
			 but nothing enforces that yet.  We use an SSAId to
			 see, whether their version remains 0 in this
			 situation. *)
	          | (Local | Label) -> SSAId (a, v, info.version)
	    with Not_found ->
	      (* FIXME: This should actually not happen, but here it may
		 indecate an inherited attribute.  The type checker should
		 provide us with the necessary information. *)
	      Messages.message 1 ("expression_to_ssa: " ^ v ^ " not found") ;
	      Id (a, v)
          end
      | StaticAttr _ as e -> e
      | Tuple (a, l) -> Tuple (a, List.map (expression_to_ssa env) l)
      | ListLit (a, l) -> ListLit (a, List.map (expression_to_ssa env) l)
      | SetLit (a, l) -> SetLit (a, List.map (expression_to_ssa env) l)
      | Unary (a, o, e) -> Unary (a, o, expression_to_ssa env e)
      | Binary (a, o, l, r) ->
	  Binary (a, o, expression_to_ssa env l, expression_to_ssa env r)
      | Expression.If (a, c, t, f) -> 
	  Expression.If (a, expression_to_ssa env c, expression_to_ssa env t,
			expression_to_ssa env f)
      | FuncCall (a, f, l) ->
	  FuncCall (a, f, List.map (expression_to_ssa env) l)
      | Expression.Label (a, l) ->
	  Expression.Label (a, expression_to_ssa env l)
      | New (a, c, l) -> New (a, c, List.map (expression_to_ssa env) l)
      | Expression.Extern _ as e -> e
      | SSAId (a, v, n) ->
	  (* We seem to rerun to_ssa, and then we just recompute all
	     assignments. *)
	  SSAId (a, v, (Hashtbl.find env v).version)
      | Phi (a, l) ->
	  (* We seem to rerun to_ssa, and then we just recompute all
	     assignments. *)
	  Phi (a, List.map (expression_to_ssa env) l)
  in
  let left_hand_side_to_ssa env =
    (* This function is used to create a new SSA name, because we
       define a new value for that variable. *)
    function
	LhsVar (n, i) ->
	  begin
	    try 
	      let info = Hashtbl.find env i in
	        match info.kind with
	            Attribute -> LhsVar (n, i) (* Attributes are unversioned *)
	          | Input ->
		      assert false (* No assignment to input variables. *)
	          | (Output | Local) ->
		      Hashtbl.replace env i { info with version = info.version + 1 } ;
		      LhsSSAId (n, i, info.version + 1)
		  | Label -> (* FIXME: Should we do more? *)
		      Hashtbl.replace env i { info with version = info.version + 1 } ;
		      LhsSSAId (n, i, info.version + 1)
            with
                Not_found ->
		  Hashtbl.add env i { kind = Label ; version = 1 } ;
		  LhsSSAId (n, i, 1)
          end
      | LhsAttr (n, s, t) -> LhsAttr (n, s, t)
      | LhsWildcard (n, t) -> LhsWildcard (n, t)
      | LhsSSAId (n, i, v) -> LhsSSAId (n, i, v)
  in
  let compute_phi note pre left right =
    Messages.message 1 ("compute_phi") ;
    let changeset = Hashtbl.create 32 in
    let find v i c =
      try
	if (Hashtbl.find pre v).version < i.version then
	  begin
	    Messages.message 1 ("compute_phi: name " ^ v ^ " changed") ;
	    Hashtbl.replace changeset v ()
	  end
	else
	  Messages.message 1
	    ("compute_phi: name " ^ v ^ " old: " ^
		(string_of_int (Hashtbl.find pre v).version) ^ " new: " ^
		(string_of_int i.version)) ;
      with
	  Not_found ->
	    Messages.message 1 ("compute_phi: new name " ^ v ) ;
	    Hashtbl.replace changeset v ()
    in
    let _ = Hashtbl.fold find left () in
    let _ = Hashtbl.fold find right () in
    let build v () (l, r) =
      let lv = try (Hashtbl.find left v).version with Not_found -> (-1)
      and rv = try (Hashtbl.find right v).version with Not_found -> (-1) in
	if lv >= 0 && rv >= 0 && lv <> rv then
	  begin
            let lhs = left_hand_side_to_ssa right
	      (LhsVar (Expression.dummy_note, v))
            in
	      (lhs :: l,
              Phi (Expression.dummy_note,
	          [SSAId (Expression.dummy_note, v, lv);
	           SSAId (Expression.dummy_note, v, rv)]) :: r)
	  end
	else
	  (l, r)
    in
      (* changeset contains all names which changed their version in left or
         right.  Now we figure out which versions we need to add. *)
    let res = Hashtbl.fold build changeset ([], []) in
      match res with
	  ([], []) -> Skip note
	| (lhs, rhs) -> Assign (note, lhs, rhs)
  in
  let rec statement_to_ssa env =
    function
	Skip n -> Skip n
      | Assert (n, e) -> Assert (n, expression_to_ssa env e)
      | Prove (n, e) -> Prove (n, expression_to_ssa env e)
      | Assign (n, lhs, rhs) ->
	  let nr = List.map (expression_to_ssa env) rhs in
	  let nl = List.map (left_hand_side_to_ssa env) lhs in
	    Assign (n, nl, nr)
      | Await (n, g) -> Await (n, expression_to_ssa env g)
      | Posit (n, g) -> Posit (n, expression_to_ssa env g)
      | Release n -> Release n
      | AsyncCall (n, None, c, m, s, a) ->
	  AsyncCall (n, None, c, m, s, List.map (expression_to_ssa env) a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let na = List.map (expression_to_ssa env) a in
	  let nl = left_hand_side_to_ssa env l in
	    AsyncCall (n, Some nl, c, m, s, na)
      | Reply (n, l, p) ->
	  let nl = expression_to_ssa env l in
	  let np = List.map (left_hand_side_to_ssa env) p in
	    Reply (n, nl, np)
      | Free (n, v) -> Free (n, List.map (expression_to_ssa env) v)
      | SyncCall (n, c, m, s, ins, outs) ->
	  let nc = expression_to_ssa env c in
	  let ni = List.map (expression_to_ssa env) ins in
	  let no = List.map (left_hand_side_to_ssa env) outs in
	    SyncCall (n, nc, m, s, ni, no)
      | AwaitSyncCall (n, c, m, s, ins, outs) ->
	  let nc = expression_to_ssa env c in
	  let ni = List.map (expression_to_ssa env) ins in
	  let no = List.map (left_hand_side_to_ssa env) outs in
	    AwaitSyncCall (n, nc, m, s, ni, no)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  (* XXX: This should not happen, but if we resolve this, we need to
	     rerun this for updating the chain... *)
	  LocalAsyncCall (n, None, m, s, ub, lb,
			 List.map (expression_to_ssa env) i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  LocalAsyncCall (n, Some (left_hand_side_to_ssa env l), m, s, ub, lb,
			 List.map (expression_to_ssa env) i)
      | LocalSyncCall (n, m, s, u, l, ins, outs) ->
	  let ni = List.map (expression_to_ssa env) ins in
	  let no = List.map (left_hand_side_to_ssa env) outs in
	    LocalSyncCall (n, m, s, u, l, ni, no)
      | AwaitLocalSyncCall (n, m, s, u, l, ins, outs) ->
	  let ni = List.map (expression_to_ssa env) ins in
	  let no = List.map (left_hand_side_to_ssa env) outs in
	    AwaitLocalSyncCall (n, m, s, u, l, ni, no)
      | Tailcall (n, m, s, u, l, ins) ->
	  let ni = List.map (expression_to_ssa env) ins in
            Tailcall (n, m, s, u, l, ni)
      | If (n, c, l, r) ->
	  let nc = expression_to_ssa env c in
	  let env_pre = Hashtbl.copy env in
	  let nl = statement_to_ssa env l in
	  let env_true = Hashtbl.copy env in
	  let nr = statement_to_ssa env r in
	  let phi = compute_phi n env_pre env_true env in
	    Sequence (n, If (n, nc, nl, nr), phi)
      | While (n, c, i, b) ->
	  let nc = expression_to_ssa env c in
	  let env_pre = Hashtbl.copy env in
	  let nb = statement_to_ssa env b in
	    (* Phi is computed like this, since we have one incoming
	       branch (env_pre), one branch if the loop is executed once,
	       and one exit branch [env].  We use the incoming branch,
	       pretending that in this case the loop has never been
	       executed.   [phi2] is a copy of phi1, but updated for the
	       exit of the loop; it is actually redundant, if we compute
	       a control flow graph.

	       XXX: Review whether this statement really holds. *)
	  let phi1 = compute_phi n env_pre env_pre env in
	  let phi2 = compute_phi n env_pre env_pre env in
	    Sequence (n, While (n, nc, i, Sequence (n, phi1, nb)), phi2)
      | Sequence (n, s1, s2) ->
	  let ns1 = statement_to_ssa env s1 in
	  let ns2 = statement_to_ssa env s2 in
	    Sequence (n, ns1, ns2)
	      (* For merge and choice we do not enforce sequencing of the
		 computation of the parts, but we allow the compiler to
		 choose some order *)
      | Merge (n, l, r) -> 
	  let env_pre = Hashtbl.copy env in
	  let nl = statement_to_ssa env l in
	  let env_left = Hashtbl.copy env in
	  let nr = statement_to_ssa env r in
	  let phi = compute_phi n env_pre env_left env in
	    Sequence (n, Merge (n, nl, nr), phi)
      | Choice (n, l, r) -> 
	  let env_pre = Hashtbl.copy env in
	  let nl = statement_to_ssa env l in
	  let env_left = Hashtbl.copy env in
	  let nr = statement_to_ssa env r in
	  let phi = compute_phi n env_pre env_left env in
	    Sequence(n, Choice (n, nl, nr), phi)
      | Extern (n, s) -> Extern (n, s)
  in
  let add_all k v tbl { VarDecl.name = name; var_type = _; init = _ } =
    (* assert (not (Hashtbl.mem tbl name)) ; *)
    if not (Hashtbl.mem tbl name) then
      Messages.message 1 ("add_all: redefining variable " ^ name) ;
    Hashtbl.add tbl name { kind = k ; version = v } ; tbl
  in
  let method_to_ssa env m =
    Messages.message 1 ("method_to_ssa: working in " ^ m.Method.name) ;
    match m.Method.body with
	None -> m
      | Some b ->
	  (* Make an environment which is specific to this method and
	     then compute an SSA format for this method *)
	  let e1 = 
	    List.fold_left (add_all Input 1) (Hashtbl.copy env)
	      m.Method.inpars
	  in
	  let e2 =
	    List.fold_left (add_all Output 0) e1 m.Method.outpars
	  in
	  let e =
	    List.fold_left (add_all Local 0) e2 m.Method.vars
	  in
	    { m with Method.body = Some (statement_to_ssa e b) }
  in
  let with_def_to_ssa env w =
    { w with With.methods = List.map (method_to_ssa env) w.With.methods }
  in
  let class_to_ssa cls =
    Messages.message 1 ("class_to_ssa: working in " ^ cls.Class.name) ;
    let tbl = Hashtbl.create 32 in
    let env =
      List.fold_left (add_all Attribute (- 1)) tbl
	(cls.Class.parameters @ cls.Class.attributes)
    in
      { cls with
	Class.with_defs = List.map (with_def_to_ssa env) cls.Class.with_defs }
  in
  let declaration_to_ssa =
    function
	Declaration.Class c -> Declaration.Class (class_to_ssa c)
      | Declaration.Interface i -> Declaration.Interface i
      | Declaration.Exception e -> Declaration.Exception e
      | Declaration.Datatype d -> Declaration.Datatype d
  in
    List.map declaration_to_ssa tree

let out_of_ssa tree =
  (** Convert a Creol tree from static single assignment form to its
      original form. *)
  let rec expression_of_ssa =
    (* A use of the SSA name.  We should be able to find the name in
       the environment. *)
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
         Bool _ | Int _ | Float _ | String _ | History _ | Id _ |
	 StaticAttr _ ) as e -> e
      | Tuple (a, l) -> Tuple (a, List.map expression_of_ssa l)
      | ListLit (a, l) -> ListLit (a, List.map expression_of_ssa l)
      | SetLit (a, l) -> SetLit (a, List.map expression_of_ssa l)
      | Unary (a, o, e) -> Unary (a, o, expression_of_ssa e)
      | Binary (a, o, l, r) ->
	  Binary (a, o, expression_of_ssa l, expression_of_ssa r)
      | Expression.If (a, c, t, f) -> 
	  Expression.If (a, expression_of_ssa c, expression_of_ssa t,
			expression_of_ssa f)
      | FuncCall (a, f, l) ->
	  FuncCall (a, f, List.map expression_of_ssa l)
      | Expression.Label (a, l) ->
	  Expression.Label (a, expression_of_ssa l)
      | New (a, c, l) -> New (a, c, List.map expression_of_ssa l)
      | Expression.Extern _ as e -> e
      | SSAId (a, v, n) -> (* Just drop the version *) Id (a, v)
      | Phi (a, l) ->
	  let same_base_p lst = List.fold_left
	    (function c ->
	      (function
		  SSAId (a, v, n) -> 
		    c && (match (List.hd lst) with
			SSAId (_, vv, _) -> v == vv
		      | _ -> assert false )
	      | _ -> assert false)) true lst
	  in
	    assert (same_base_p l) ; expression_of_ssa (List.hd l)
  in
  let left_hand_side_of_ssa =
    (* This function is used to create a new SSA name, because we
       define a new value for that variable. *)
    function
	LhsVar _ as l -> l
      | LhsAttr (n, s, t) -> LhsAttr (n, s, t)
      | LhsWildcard (n, t) -> LhsWildcard (n, t)
      | LhsSSAId (n, i, v) -> LhsVar (n, i)
  in
  let rec statement_of_ssa =
    function
	Skip n -> Skip n
      | Assert (n, e) -> Assert (n, expression_of_ssa e)
      | Prove (n, e) -> Prove (n, expression_of_ssa e)
      | Assign (n, lhs, rhs) ->
	  let nr = List.map expression_of_ssa rhs in
	  let nl = List.map left_hand_side_of_ssa lhs in
	    (* FIXME: This may give rise to identity assignments (caused by
	       introducing Phi notes, which we want to eliminate. *)
	    Statement.simplify_assignment (Assign (n, nl, nr))
      | Await (n, g) -> Await (n, expression_of_ssa g)
      | Posit (n, g) -> Posit (n, expression_of_ssa g)
      | Release n -> Release n
      | AsyncCall (n, None, c, m, s, a) ->
	  AsyncCall (n, None, c, m, s, List.map expression_of_ssa a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let na = List.map expression_of_ssa a in
	  let nl = left_hand_side_of_ssa l in
	    AsyncCall (n, Some nl, c, m, s, na)
      | Reply (n, l, p) ->
	  let nl = expression_of_ssa l in
	  let np = List.map left_hand_side_of_ssa p in
	    Reply (n, nl, np)
      | Free (n, v) -> Free (n, List.map expression_of_ssa v)
      | SyncCall (n, c, m, s, ins, outs) ->
	  let nc = expression_of_ssa c in
	  let ni = List.map expression_of_ssa ins in
	  let no = List.map left_hand_side_of_ssa outs in
	    SyncCall (n, nc, m, s, ni, no)
      | AwaitSyncCall (n, c, m, s, ins, outs) ->
	  let nc = expression_of_ssa c in
	  let ni = List.map expression_of_ssa ins in
	  let no = List.map left_hand_side_of_ssa outs in
	    AwaitSyncCall (n, nc, m, s, ni, no)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  (* XXX: This should not happen, but if we resolve this, we need to
	     rerun this for updating the chain... *)
	  LocalAsyncCall (n, None, m, s, ub, lb, List.map expression_of_ssa i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  LocalAsyncCall (n, Some (left_hand_side_of_ssa l), m, s, ub, lb,
			 List.map expression_of_ssa i)
      | LocalSyncCall (n, m, s, u, l, ins, outs) ->
	  let ni = List.map expression_of_ssa ins in
	  let no = List.map left_hand_side_of_ssa outs in
	    LocalSyncCall (n, m, s, u, l, ni, no)
      | AwaitLocalSyncCall (n, m, s, u, l, ins, outs) ->
	  let ni = List.map expression_of_ssa ins in
	  let no = List.map left_hand_side_of_ssa outs in
	    AwaitLocalSyncCall (n, m, s, u, l, ni, no)
      | Tailcall (n, m, s, u, l, ins) ->
	  let ni = List.map expression_of_ssa ins in
	    Tailcall (n, m, s, u, l, ni)
      | If (n, c, l, r) ->
	  let nc = expression_of_ssa c in
	  let nl = statement_of_ssa l in
	  let nr = statement_of_ssa r in
	    If (n, nc, nl, nr)
      | While (n, c, i, b) ->
	  let nc = expression_of_ssa c in
	  let nb = statement_of_ssa b in
	    While (n, nc, i, nb)
      | Sequence (n, s1, s2) ->
	  let ns1 = statement_of_ssa s1 in
	  let ns2 = statement_of_ssa s2 in
	    Sequence (n, ns1, ns2)
	      (* For merge and choice we do not enforce sequencing of the
		 computation of the parts, but we allow the compiler to
		 choose some order *)
      | Merge (n, l, r) -> 
	  let nl = statement_of_ssa l in
	  let nr = statement_of_ssa r in
	    Merge (n, nl, nr)
      | Choice (n, l, r) -> 
	  let nl = statement_of_ssa l in
	  let nr = statement_of_ssa r in
	    Choice (n, nl, nr)
      | Extern (n, s) -> Extern (n, s)
  in
  let method_of_ssa m =
    Messages.message 1 ("method_of_ssa: working in " ^ m.Method.name) ;
    match m.Method.body with
	None -> m
      | Some b ->
	    { m with Method.body =
	      Some (Statement.remove_redundant_skips (statement_of_ssa b)) }
  in
  let with_def_of_ssa w =
    { w with With.methods = List.map method_of_ssa w.With.methods }
  in
  let class_of_ssa cls =
    Messages.message 1 ("class_of_ssa: working in " ^ cls.Class.name) ;
      { cls with
	Class.with_defs = List.map with_def_of_ssa cls.Class.with_defs }
  in
  let declaration_of_ssa =
    function
	Declaration.Class c -> Declaration.Class (class_of_ssa c)
      | Declaration.Interface i -> Declaration.Interface i
      | Declaration.Exception e -> Declaration.Exception e
      | Declaration.Datatype d -> Declaration.Datatype d
  in
    List.map declaration_of_ssa tree
