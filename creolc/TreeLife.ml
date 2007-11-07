(*
 * TreeLife.ml -- Tree-based life variable analysis for Creol programs
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

(*s Compute life ranges of variables in Creol programs.

  A variable is called \emph{life} at a statement $s$, if it may be
  read before the next write to it.

  The function [generate] computes the set of variables \emph{read} in
  a statement, which usually happens only by expressions.  The
  function [kill] computes the set of variables \emph{written to} in a
  statement.
*)

open Creol
open Expression
open Statement


(* Log messages for lifeness analysis *)
let log l = Messages.message (l + 0)


(* Add a set of variables to the current result set. *)
let add f s e = IdSet.union (f e) s


(* Compute the generate sets of a method body by traversing it forward. *)
let compute_generates ~program ~cls ~meth =
  let () = Messages.message 2 ("Compute generates in " ^ meth.Method.name) in
  let rec generate =
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
	    Bool _ | Int _ | Float _ | String _ | History _) -> IdSet.empty
      | Id (a, v) when Method.local_p meth v ->
	  IdSet.singleton v
      | Id (a, v) ->
	  IdSet.empty
      | StaticAttr _ ->
	  IdSet.empty
      | Tuple (a, l) ->
	  List.fold_left (add generate) IdSet.empty l
      | ListLit (a, l) ->
	  List.fold_left (add generate) IdSet.empty l
      | SetLit (a, l) ->
	  List.fold_left (add generate) IdSet.empty l
      | Unary (a, o, e) ->
	  generate e
      | Binary (a, o, l, r) ->
	  IdSet.union (generate l) (generate r)
      | Expression.If (a, c, t, f) ->
	  List.fold_left (add generate) IdSet.empty [c; t; f]
      | FuncCall (a, f, l) ->
	  List.fold_left (add generate) IdSet.empty l
      | Expression.Label (a, l) ->
	  generate l
      | New (a, c, l) ->
	  List.fold_left (add generate) IdSet.empty l
      | Expression.Extern _ ->
	  IdSet.empty
      | SSAId (a, v, n) ->
	  assert (Method.local_p meth v); IdSet.singleton v
      | Phi (a, l) ->
	  List.fold_left (add generate) IdSet.empty l
  in
  let kill =
    function
	LhsId (n, i) when Method.local_p meth i -> IdSet.singleton i
      | LhsId (n, i) -> IdSet.empty
      | LhsAttr (n, s, t) -> IdSet.empty
      | LhsWildcard (n, t) -> IdSet.empty
      | LhsSSAId (n, i, v) -> assert (Method.local_p meth i); IdSet.singleton i
  in
  let rec compute_in_statement outs =
    function
	Skip n ->
	  Skip { n with life = outs }
      | Assert (n, e) ->
	  let n' = { n with life = IdSet.union outs (generate e) } in
	    Assert (n', e)
      | Prove (n, e) ->
	  let n' = { n with life = IdSet.union outs (generate e) } in
	    Prove (n', e)
      | Assign (n, lhs, rhs) ->
	  let k = List.fold_left (add kill) IdSet.empty lhs
	  and g = List.fold_left (add generate) IdSet.empty rhs in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g } in
	    Assign (n', lhs, rhs)
      | Await (n, g) ->
	  let n' = { n with life = IdSet.union outs (generate g) } in
	    Await (n', g)
      | Posit (n, g) ->
	  let n' = { n with life = IdSet.union outs (generate g) } in
	    Posit (n', g)
      | Release n ->
	  Release { n with life = outs }
      | AsyncCall (n, None, c, m, s, a) ->
	  let g = 
	    IdSet.union outs (List.fold_left (add generate) IdSet.empty (c::a))
	  in
	    AsyncCall ({ n with life = g }, None, c, m, s, a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let g = List.fold_left (add generate) IdSet.empty (c::a)
	  and k =  kill l in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g } in
	    AsyncCall (n', Some l, c, m, s, a)
      | Reply (n, l, p) ->
	  let k = List.fold_left (add kill) IdSet.empty p in
	  let n' = { n with life = IdSet.diff outs k } in
	    Reply (n', l, p)
      | Free (n, v) ->
	  let k = List.fold_left (add kill) IdSet.empty v in
	  let n' = { n with life = IdSet.diff outs k } in
	    Free (n', v)
      | Bury (n, v) ->
	  (* This statement must not affect the life range of any value,
	     and all its arguments must be dead at that point. *)
	  let k = List.fold_left (add kill) IdSet.empty v in
	  let n' = { n with life = IdSet.diff outs k } in
	    Bury (n', v)
      | SyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add generate) IdSet.empty (c::i)
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g } in
	    SyncCall (n', c, m, s, i, o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add generate) IdSet.empty (c::i)
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g } in
	    AwaitSyncCall (n', c, m, s, i, o)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  let g = List.fold_left (add generate) IdSet.empty i in
	  let n' = { n with life = IdSet.union outs g } in
	    LocalAsyncCall (n', None, m, s, ub, lb, i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  let g = List.fold_left (add generate) IdSet.empty i
	  and k = kill l in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g } in
	    LocalAsyncCall (n', Some l, m, s, ub, lb, i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add generate) IdSet.empty i
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g }
	  in
	    LocalSyncCall (n', m, s, u, l, i, o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add generate) IdSet.empty i
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union (IdSet.diff outs k) g } in
	    AwaitLocalSyncCall (n', m, s, u, l, i, o)
      | Tailcall (n, m, s, u, l, ins) ->
	  let g =
	    IdSet.union outs (List.fold_left (add generate) IdSet.empty ins)
	  in
	  let n' = { n with life = IdSet.union outs g } in
	    Tailcall (n', m, s, u, l, ins)
      | If (n, c, l, r) ->
	  let c' = IdSet.union outs (generate c) in
	  let l' = compute_in_statement c' l
	  and r' = compute_in_statement c' r in
	  let n' =
	    { n with life = IdSet.union (note l').life (note r').life }
	  in
	    If (n', c, l', r')
      | While (n, c, i, b) ->
	  let c' = IdSet.union outs (generate c) in
	  let i' =
 	    match i with
		None -> c'
	      | Some inv -> IdSet.union c' (generate inv)
	  in
	  let b' = compute_in_statement i' b in
	  let n' = { n with life = (note b').life } in
	    While (n', c, i, b')
      | Sequence (n, s1, s2) ->
	  let s2' = compute_in_statement outs s2 in
	  let s1' = compute_in_statement (note s2').life s1 in
	  let n' = { n with life = (note s2').life } in
	    Sequence (n', s1', s2')
      | Merge (n, s1, s2) -> 
	  let s1' = compute_in_statement outs s1
	  and s2' = compute_in_statement outs s2 in
	  let n' =
	    { n with life = IdSet.union (note s1').life (note s2').life }
	  in
	    Merge (n', s1', s2')
      | Choice (n, s1, s2) -> 
	  let s1' = compute_in_statement outs s1
	  and s2' = compute_in_statement outs s2 in
	  let n' =
	    { n with life = IdSet.union (note s1').life (note s2').life }
	  in
	    Choice (n', s1', s2')
      | Extern (n, s) ->
	  Extern ({ n with life = outs }, s)
  in
    match meth.Method.body with
	None -> meth
      | Some b ->
	  let add s v = IdSet.add v.VarDecl.name s in
	  let outs = List.fold_left add IdSet.empty meth.Method.outpars in
	    { meth with Method.body = Some (compute_in_statement outs b) }

(* Compute the kill sets of a method body by traversing it backwards.
   This pass is necessary for programs which are not in SSA form.  For
   all other programs, this pass will do nothing.  It hsould be
   reasonably fast, so this should not cost too much.  *)

let compute_kills ~program ~cls ~meth =
  let () = Messages.message 2 ("Compute kills in " ^ meth.Method.name) in
    meth

let compute_in_method ~program ~cls ~meth =
  let () = Messages.message 2
    ("Compute life ranges in " ^ cls.Class.name ^ "::" ^ meth.Method.name)
  in
    match meth.Method.body with
	None -> meth
      | Some b ->
	  compute_kills program cls (compute_generates program cls meth)

(* Compute life ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let analyse program =
  let compute_in_declaration d =
    let compute_in_class cls =
      let compute_in_with_def w =
	{ w with With.methods =
	    List.map (fun m -> compute_in_method program cls m) w.With.methods }
      in
	{ cls with Class.with_defs =
	    List.map compute_in_with_def cls.Class.with_defs }
    in
      match d with
	  Declaration.Class c -> Declaration.Class (compute_in_class c)
	| Declaration.Interface _ -> d
	| Declaration.Exception _ -> d
	| Declaration.Datatype _ -> d
	| Declaration.Function _ -> d
  in
    List.map compute_in_declaration program
