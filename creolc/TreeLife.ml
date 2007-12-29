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
  read before the next write to it.  This can be computed with the
  data-flow equation
  \begin{equation*}
    \mathit{live}_{\mathit{in}}(s)= \mathit{gen}(s)\cup
    (\mathit{life}_{\mathit{out}}(s)\setminus \mathit{kill}(s))\quad,
  \end{equation*}
  where $\mathit{life}_{\mathit{out}}(s)=
  \bigcup_{p\in\mathit{succ}(s)}\mathit{life}_{\mathit{in}}(p)$.  The set 
  $\mathit{life}_{\mathit{out}}(\mathit{final})$ is equal to the
  out-parameters of the method (these are always life in a method).

  The function [gen] computes the set of variables \emph{read} in
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


(* Write the input and output set of a statement. *)

let logio stmt i o =
  if !Messages.verbose > 0 then (* Avoid this if no output is requested. *)
    let g s =
      let rec h =
	function
	    [] -> ""
	  | [e] -> e
	  | e::r -> e ^ ", " ^ (h r)
      in
	h (IdSet.fold (fun e a -> e :: a) s [])
    in
    let w = (file stmt) ^ ": " ^ (string_of_int (line stmt)) in
      log 1 ("Live at " ^ w ^ " [" ^ (Statement.to_string  stmt) ^
	       "]: in = {" ^ (g i) ^ "}, out = {" ^ (g o) ^ "}")


(* Compute life ranges of a method body by traversing it backward. *)

let compute_in_body ~program ~cls ~meth =
  let rec gen =
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
	  List.fold_left (add gen) IdSet.empty l
      | ListLit (a, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | SetLit (a, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | Unary (a, o, e) ->
	  gen e
      | Binary (a, o, l, r) ->
	  IdSet.union (gen l) (gen r)
      | Expression.If (a, c, t, f) ->
	  List.fold_left (add gen) IdSet.empty [c; t; f]
      | FuncCall (a, f, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | Expression.Label (a, l) ->
	  gen l
      | New (a, c, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | Expression.Extern _ ->
	  IdSet.empty
      | SSAId (a, v, n) ->
	  assert (Method.local_p meth v); IdSet.singleton v
      | Phi (a, l) ->
	  List.fold_left (add gen) IdSet.empty l
  in
  let kill =
    function
	LhsId (n, i) when Method.local_p meth i -> IdSet.singleton i
      | LhsId (n, i) -> IdSet.empty
      | LhsAttr (n, s, t) -> IdSet.empty
      | LhsWildcard (n, t) -> IdSet.empty
      | LhsSSAId (n, i, v) -> assert (Method.local_p meth i); IdSet.singleton i
  in
  let rec compute_in_statement outs stmt =
    match stmt with
	Skip n ->
	  let n' = { n with life = outs } in
	    logio stmt outs n'.life ;
	    Skip n'
      | Assert (n, e) ->
	  let g = gen e in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    Assert (n', e)
      | Prove (n, e) ->
	  let g = gen e in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    Prove (n', e)
      | Assign (n, lhs, rhs) ->
	  let k = List.fold_left (add kill) IdSet.empty lhs
	  and g = List.fold_left (add gen) IdSet.empty rhs in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    Assign (n', lhs, rhs)
      | Await (n, c) ->
	  let g = gen c in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    Await (n', c)
      | Posit (n, c) ->
	  let g = gen c in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    Posit (n', c)
      | Release n ->
	  let n' = { n with life = outs } in
	    logio stmt outs n'.life ;
	    Release n'
      | AsyncCall (n, None, c, m, s, a) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::a) in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    AsyncCall (n', None, c, m, s, a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::a)
	  and k =  kill l in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    AsyncCall (n', Some l, c, m, s, a)
      | Reply (n, l, p) ->
	  let g = gen l in
	  let k = List.fold_left (add kill) IdSet.empty p in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    Reply (n', l, p)
      | Free (n, v) ->
	  (* This statement keeps its arguments life, even though the
	     list of variables here is to be released. The call to [kill]
	     is used for typing reasons only. *)
	  let g = List.fold_left (add kill) IdSet.empty v in
	  let n' = { n with life = IdSet.union outs g } in
	    logio stmt outs n'.life ;
	    Free (n', v)
      | Bury (n, v) ->
	  (* This statement must not affect the life range of any value,
	     and all its arguments must be dead at that point. *)
	  let k = List.fold_left (add kill) IdSet.empty v in
	  let n' = { n with life = IdSet.diff outs k } in
	    logio stmt outs n'.life ;
	    Bury (n', v)
      | SyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::i)
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    SyncCall (n', c, m, s, i, o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::i)
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    AwaitSyncCall (n', c, m, s, i, o)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  let g = List.fold_left (add gen) IdSet.empty i in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    LocalAsyncCall (n', None, m, s, ub, lb, i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  let g = List.fold_left (add gen) IdSet.empty i
	  and k = kill l in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    LocalAsyncCall (n', Some l, m, s, ub, lb, i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty i
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) }
	  in
	    logio stmt outs n'.life ;
	    LocalSyncCall (n', m, s, u, l, i, o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty i
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with life = IdSet.union g (IdSet.diff outs k) } in
	    logio stmt outs n'.life ;
	    AwaitLocalSyncCall (n', m, s, u, l, i, o)
      | Tailcall (n, m, s, u, l, ins) ->
	  let g = List.fold_left (add gen) IdSet.empty ins in
	  let n' = { n with life = IdSet.union g outs } in
	    logio stmt outs n'.life ;
	    Tailcall (n', m, s, u, l, ins)
      | If (n, c, l, r) ->
	  let l' = compute_in_statement outs l
	  and r' = compute_in_statement outs r in
	  let outs' = IdSet.union (life l') (life r') in
	  let g = gen c in
	  let n' = { n with life = IdSet.union g outs' }
	  in
	    logio stmt outs n'.life ;
	    If (n', c, l', r')
      | While (n, c, i, b) ->
	  let b' = compute_in_statement outs b in
	  let outs' = life b' in
	  let g =
 	    match i with
		None -> (gen c)
	      | Some inv -> IdSet.union (gen c) (gen inv)
	  in
	  let n' = { n with life = IdSet.union g outs' } in
	    logio stmt outs n'.life ;
	    While (n', c, i, b')
      | Sequence (n, s1, s2) ->
	  let s2' = compute_in_statement outs s2 in
	  let s1' = compute_in_statement (life s2') s1 in
	    (* the out of the statement is the out of the first statement. *)
	  let n' = { n with life = life s1' } in
	    logio stmt outs n'.life ;
	    Sequence (n', s1', s2')
      | Merge (n, s1, s2) -> 
	  let s1' = compute_in_statement outs s1
	  and s2' = compute_in_statement outs s2 in
	  let outs' = IdSet.union (life s1') (life s2') in
	  let n' = { n with life = outs' } in
	    logio stmt outs n'.life ;
	    Merge (n', s1', s2')
      | Choice (n, s1, s2) -> 
	  let s1' = compute_in_statement outs s1
	  and s2' = compute_in_statement outs s2 in
	  let outs' = IdSet.union (life s1') (life s2') in
	  let n' = { n with life = outs' } in
	    logio stmt outs n'.life ;
	    Choice (n', s1', s2')
      | Extern (n, s) ->
	  let n' = { n with life = outs } in
	    logio stmt outs n'.life ;
	    Extern (n', s)
  in
    match meth.Method.body with
	None -> meth
      | Some b ->
	  let () = log 1 ("Live vars in " ^ (Method.name_as_string meth)) in
	  let add s v = IdSet.add v.VarDecl.name s in
	  let outs = List.fold_left add IdSet.empty meth.Method.outpars in
	    { meth with Method.body = Some (compute_in_statement outs b) }


let compute_in_method ~program ~cls ~meth =
  let () = Messages.message 2
    ("Compute life ranges in " ^ cls.Class.name ^ "::" ^ meth.Method.name)
  in
    match meth.Method.body with
	None -> meth
      | Some b -> compute_in_body program cls meth


(* Compute life ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let analyse program =
  let compute_in_declaration d =
    let compute_in_class cls =
      let compute_in_with_def w =
	{ w with With.methods =
	    List.map (fun m -> compute_in_method program cls m)
	      w.With.methods }
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
