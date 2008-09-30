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

(*s Compute a Creol program in \emph{static single assignment form} from
  a Creol program.

  
*)

open Creol
open Expression
open Statement

(* The information we want to collect about variables during analysis *)

type kind = Attribute | Input | Output | Local | Label

(* The type of the environment used to compute the SSA. *)

module Env = Map.Make(String)


(* Convert a Creol tree into \emph{static single assignment} form.

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

   \textbf{TO DO}: We need to find out how we can come up with a clever
   implementation for merge statements.  We may need to expand the
   merge statements into choice statements.  For now, we assume
   that there is {i no} assignment to local variables within merge
   statements, if they are also used within the merge statement.
*)

let into_ssa program =
  let rec expression_to_ssa meth env =
    (* A use of the SSA name.  We should be able to find the name in
       the environment. *)
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
         Bool _ | Int _ | Float _ | String _ | History _ | ObjLit _) as e -> e
      | Id (n, name) when Method.local_p meth name ->
	  SSAId (n, name, Env.find name env)
      | Id (n, name) ->
	  Id (n, name)
      | StaticAttr _ as e -> e
      | Tuple (a, l) -> Tuple (a, List.map (expression_to_ssa meth env) l)
      | ListLit (a, l) -> ListLit (a, List.map (expression_to_ssa meth env) l)
      | SetLit (a, l) -> SetLit (a, List.map (expression_to_ssa meth env) l)
      | Unary (a, o, e) -> Unary (a, o, expression_to_ssa meth env e)
      | Binary (a, o, l, r) ->
	  Binary (a, o, expression_to_ssa meth env l, expression_to_ssa meth env r)
      | Expression.If (a, c, t, f) -> 
	  Expression.If (a, expression_to_ssa meth env c, expression_to_ssa meth env t,
			expression_to_ssa meth env f)
      | FuncCall (a, f, l) ->
	  FuncCall (a, f, List.map (expression_to_ssa meth env) l)
      | Expression.Label (a, l) ->
	  Expression.Label (a, expression_to_ssa meth env l)
      | New (a, c, l) -> New (a, c, List.map (expression_to_ssa meth env) l)
      | Choose (n, v, t, e) ->
	  (* [v] is actually a binder and should not be converted to SSA. *)
	  Choose (n, v, t, expression_to_ssa meth env e)
      | Exists (n, v, t, e) ->
	  (* [v] is actually a binder and should not be converted to SSA. *)
	  Exists (n, v, t, expression_to_ssa meth env e)
      | Forall (n, v, t, e) ->
	  (* [v] is actually a binder and should not be converted to SSA. *)
	  Forall (n, v, t, expression_to_ssa meth env e)
      | LabelLit (a, l) ->
	  LabelLit (a, List.map (expression_to_ssa meth env) l)
      | Expression.Extern _ as e -> e
      | (SSAId _ | Phi _) as e -> e
  in
  let lhs_to_ssa meth env =
    (* This function is used to create a new SSA name, because we
       define a new value for that variable. *)
    function
	LhsId (n, name) when Method.local_p meth name ->
	  let version = Env.find name env in
	    (Env.add name (version + 1) env, LhsSSAId (n, name, version + 1))
      | (LhsId _ | LhsAttr _ | LhsWildcard _) as l -> (env, l)
      | LhsSSAId _ -> assert false
  in
  let lhs_list_to_ssa meth env ll =
    let f (e, l) id = let (e', id') = lhs_to_ssa meth e id in (e', id'::l) in
    let (env', ll') = List.fold_left f (env, []) ll in
      (env', List.rev ll')
  in
  let compute_phi note pre left right =

    (* Currently, a $\phi$ node is generated for every point in which
       control merges.  This merge point has exactly two incoming
       paths, here called [left] and [right]. A Phi assignment is only
       needed for those names, which are different in both paths.  *)
    Messages.message 1 ("compute_phi") ;
    let module S = Set.Make(String) in
    let changed pre post =
      let f n v cs =
	   if (Env.find n pre) = v then
	     cs
	   else
	     begin
	       Messages.message 1 ("compute_phi: name " ^ n ^ " changed") ;
	       S.add n cs
	     end
      in
	Env.fold f post S.empty
    in

    (* changeset contains all names which changed their version in left or
       right.  Now we figure out which versions we need to add. *)

    let changeset = S.union (changed pre left) (changed pre right) in

    (* Build the left-hand and righthand side of the phi node. *)
      if S.is_empty changeset then
	Skip note
      else
	let (lhs, rhs) =
	  let f name (l, r) =
	    let lv = (Env.find name left) and rv = (Env.find name right) in
	      assert (lv <> rv) ;
	      ((LhsId (Expression.make_note (), name)) :: l,
	       Phi (Expression.make_note (),
	            [SSAId (Expression.make_note (), name, lv);
	             SSAId (Expression.make_note (), name, rv)]) :: r)
	  in
	    S.fold f changeset ([], [])
	in
	  Assign (note, lhs, rhs)
  in
  let rec statement_to_ssa meth env =
    function
	Skip n ->
	  (env, Skip n)
      | Assert (n, e) ->
	  (env, Assert (n, expression_to_ssa meth env e))
      | Prove (n, e) ->
	  (env, Prove (n, expression_to_ssa meth env e))
      | Assign (n, lhs, rhs) ->
	  let rhs' = List.map (expression_to_ssa meth env) rhs in
	  let (env', lhs') = lhs_list_to_ssa meth env lhs in
	    (env', Assign (n, lhs', rhs'))
      | Await (n, g) ->
	  (env, Await (n, expression_to_ssa meth env g))
      | Posit (n, g) ->
	  (env, Posit (n, expression_to_ssa meth env g))
      | Release n ->
	  (env, Release n)
      | AsyncCall (n, None, c, m, s, a) ->
	  let a' = List.map (expression_to_ssa meth env) a in
	  (env, AsyncCall (n, None, c, m, s, a'))
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let a' = List.map (expression_to_ssa meth env) a in
	  let (env', l') = lhs_to_ssa meth env l in
	    (env', AsyncCall (n, Some l', c, m, s, a'))
      | Get (n, l, p) ->
	  let l' = expression_to_ssa meth env l in
	  let (env', p') = lhs_list_to_ssa meth env p in
	    (env', Get (n, l', p'))
      | Free (n, v) ->
	  let (env', v') = lhs_list_to_ssa meth env v in
	    (env', Free (n, v'))
      | Bury (n, v) ->
	  let (env', v') = lhs_list_to_ssa meth env v in
	    (env', Bury (n, v'))
      | SyncCall (n, c, m, s, i, o) ->
	  let c' = expression_to_ssa meth env c in
	  let i' = List.map (expression_to_ssa meth env) i in
	  let (env', o') = lhs_list_to_ssa meth env o in
	    (env', SyncCall (n, c', m, s, i', o'))
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  let c' = expression_to_ssa meth env c in
	  let i' = List.map (expression_to_ssa meth env) i in
	  let (env', o') = lhs_list_to_ssa meth env o in
	    (env', AwaitSyncCall (n, c', m, s, i', o'))
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  let i' = List.map (expression_to_ssa meth env) i in
	    (env, LocalAsyncCall (n, None, m, s, ub, lb, i'))
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  let i' = List.map (expression_to_ssa meth env) i in
	  let (env', l') = lhs_to_ssa meth env l in
	    (env', LocalAsyncCall (n, Some l', m, s, ub, lb, i'))
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  let i' = List.map (expression_to_ssa meth env) i in
	  let (env', o') = lhs_list_to_ssa meth env o in
	    (env', LocalSyncCall (n, m, s, u, l, i', o))
      | AwaitLocalSyncCall (n, m, s, ub, lb, i, o) ->
	  let i' = List.map (expression_to_ssa meth env) i in
	  let (env', o') = lhs_list_to_ssa meth env o in
	    (env', AwaitLocalSyncCall (n, m, s, ub, lb, i', o'))
      | MultiCast (a, c, m, s, i) ->
	  let c' = expression_to_ssa meth env c
	  and i' = List.map (expression_to_ssa meth env) i
	  in
	    (env, MultiCast (a, c', m, s, i'))
      | Discover (a, t, m, s, i) ->
	  let i' = List.map (expression_to_ssa meth env) i in
	    (env, Discover (a, t, m, s, i'))
      | Tailcall (n, c, m, s, i) ->
	  let c' = expression_to_ssa meth env c
	  and i' = List.map (expression_to_ssa meth env) i
	  in
            (env, Tailcall (n, c', m, s, i'))
      | StaticTail (n, m, s, ub, lb, i) ->
	  let i' = List.map (expression_to_ssa meth env) i in
            (env, StaticTail (n, m, s, ub, lb, i'))
      | If (n, c, l, r) ->
	  let nc = expression_to_ssa meth env c in
	  let (env_l, nl) = statement_to_ssa meth env l in
	  let (env_r, nr) = statement_to_ssa meth env_l r in
	  let ass = compute_phi n env env_l env_r in
	  let (env', phi) = statement_to_ssa meth env_r ass in
	    (env', Sequence (n, If (n, nc, nl, nr), phi))
      | While (n, c, i, b) ->
	  (* Because there is one incoming branch [env] to the while
	     statement, one branch [env_b] at the exit of the loop,
	     so $\phi_1$ has to be updated at the head of the loop
	     to compute the incoming values.

	     once, and one exit
	     branch [env_e].  We use the incoming branch, pretending
	     that in this case the loop has never been executed.
	     [phi2] is the $\phi$-assignment at the exit of the
	     loop. *)
	  let c' = expression_to_ssa meth env c in
	  let i' = expression_to_ssa meth env i in
	  let (env_b, b') = statement_to_ssa meth env b in
	  let ass1 = compute_phi n env env env_b in
	  let (e1, p1) = statement_to_ssa meth env ass1 in
	  let b'' = While (n, c', i', Sequence (n, p1, b')) in
	  let ass2 = compute_phi n env e1 env_b in
	  let (e2, p2) = statement_to_ssa meth env ass2 in
	    (e2, Sequence (n, b'', p2))
      | DoWhile _ -> assert false
      | Return (n, r) ->
	  let r' = List.map (expression_to_ssa meth env) r in
	    (env, Return (n, r'))
      | Continue _ -> assert false
      | Sequence (n, s1, s2) ->
	  let (e1, s1') = statement_to_ssa meth env s1 in
	  let (e2, s2') = statement_to_ssa meth e1 s2 in
	    (e2, Sequence (n, s1', s2'))
      | Choice (n, l, r) -> 
          let (el, l') = statement_to_ssa meth env l in
          let (er, r') = statement_to_ssa meth el r in
	  let ass = compute_phi n env el er in
	  let (env', phi) = statement_to_ssa meth er ass in
	    (env', Sequence(n, Choice (n, l', r'), phi))
      | Extern (n, s) -> (env, Extern (n, s))
  in
  let method_to_ssa meth =
    let add tbl { VarDecl.name = name } =
      if (Env.mem name tbl) then
	begin
	  Messages.message 1 ("add: redefining variable " ^ name) ;
	  tbl
	end
      else
	Env.add name 0 tbl
    in
      Messages.message 1 ("method_to_ssa: working in " ^ meth.Method.name) ;
      match meth.Method.body with
	  None -> meth
	| Some b ->
	    (* Make an environment which is specific to this method and
	       then compute an SSA format for this method *)
	    let e1 = List.fold_left add Env.empty meth.Method.inpars in
	    let e2 = List.fold_left add e1 meth.Method.outpars in
	    let env = List.fold_left add e2 meth.Method.vars in
	    let (_, b') = statement_to_ssa meth env b in
	      { meth with Method.body = Some b' }
  in
  let with_def_to_ssa w =
    { w with With.methods = List.map method_to_ssa w.With.methods }
  in
  let class_to_ssa cls =
    Messages.message 1 ("class_to_ssa: working in " ^ cls.Class.name) ;
    { cls with Class.with_defs = List.map with_def_to_ssa cls.Class.with_defs }
  in
  let declaration_to_ssa =
    function
	Declaration.Class c -> Declaration.Class (class_to_ssa c)
      | (Declaration.Interface _
	| Declaration.Exception _
	| Declaration.Datatype _
	| Declaration.Function _
	| Declaration.Object _) as d -> d
  in
    List.map declaration_to_ssa program

let out_of_ssa tree =
  (** Convert a Creol tree from static single assignment form to its
      original form. *)
  let rec expression_of_ssa =
    (* A use of the SSA name.  We should be able to find the name in
       the environment. *)
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
         Bool _ | Int _ | Float _ | String _ | History _ | Id _ |
	 StaticAttr _ | ObjLit _) as e -> e
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
      | Choose (n, v, t, e) ->
	  (* [v] is actually a binder and should not have been converted
	     to SSA. *)
	  Choose (n, v, t, expression_of_ssa e)
      | Exists (n, v, t, e) ->
	  (* [v] is actually a binder and should not have been converted
	     to SSA. *)
	  Exists (n, v, t, expression_of_ssa e)
      | Forall (n, v, t, e) ->
	  (* [v] is actually a binder and should not have been converted
	     to SSA. *)
	  Forall (n, v, t, expression_of_ssa e)
      | LabelLit (a, l) -> LabelLit (a, List.map expression_of_ssa l)
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
	LhsId _ as l -> l
      | LhsAttr (n, s, t) -> LhsAttr (n, s, t)
      | LhsWildcard (n, t) -> LhsWildcard (n, t)
      | LhsSSAId (n, i, v) -> LhsId (n, i)
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
      | Get (n, l, p) ->
	  let nl = expression_of_ssa l in
	  let np = List.map left_hand_side_of_ssa p in
	    Get (n, nl, np)
      | Free (n, v) -> Free (n, List.map left_hand_side_of_ssa v)
      | Bury (n, v) -> Bury (n, List.map left_hand_side_of_ssa v)
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
      | MultiCast (a, c, m, s, i) ->
	  let c' = expression_of_ssa c
	  and i' = List.map expression_of_ssa i
	  in
            MultiCast (a, c', m, s, i')
      | Discover (a, t, m, s, i) ->
	  let i' = List.map expression_of_ssa i in
            Discover (a, t, m, s, i')
      | Tailcall (n, c, m, s, i) ->
	  let c' = expression_of_ssa c
	  and i' = List.map expression_of_ssa i
	  in
	    Tailcall (n, c', m, s, i')
      | StaticTail (n, m, s, u, l, i) ->
	  let i' = List.map expression_of_ssa i in
	    StaticTail (n, m, s, u, l, i')
      | Return (n, r) ->
	  let r' = List.map expression_of_ssa r in
	    Return (n, r')
      | Continue _ -> assert false
      | If (n, c, l, r) ->
	  let nc = expression_of_ssa c in
	  let nl = statement_of_ssa l in
	  let nr = statement_of_ssa r in
	    If (n, nc, nl, nr)
      | While (n, c, i, b) ->
	  let nc = expression_of_ssa c in
	  let nb = statement_of_ssa b in
	    While (n, nc, i, nb)
      | DoWhile _ -> assert false
      | Sequence (n, s1, s2) ->
	  let ns1 = statement_of_ssa s1 in
	  let ns2 = statement_of_ssa s2 in
	    Sequence (n, ns1, ns2)
      | Choice (n, l, r) -> 
	  let nl = statement_of_ssa l
          and nr = statement_of_ssa r in
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
      | Declaration.Class c -> Declaration.Class (class_of_ssa c)
      | (Declaration.Interface _
	| Declaration.Exception _
	| Declaration.Datatype _
	| Declaration.Function _
	| Declaration.Object _) as d -> d
  in
    List.map declaration_of_ssa tree
