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
let log l = Messages.message (l + 2)

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
      | Id (_, v)  ->
	  if Method.local_p meth v then IdSet.singleton v else IdSet.empty
      | StaticAttr _ ->
	  IdSet.empty
      | Tuple (_, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | ListLit (_, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | SetLit (_, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | Unary (_, _, e) ->
	  gen e
      | Binary (_, _, l, r) ->
	  IdSet.union (gen l) (gen r)
      | Expression.If (_, c, t, f) ->
	  List.fold_left (add gen) IdSet.empty [c; t; f]
      | FuncCall (_, _, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | Expression.Label (_, l) ->
	  gen l
      | New (_, _, l) ->
	  List.fold_left (add gen) IdSet.empty l
      | Choose (_, _, _, e) | Exists (_, _, _, e) | Forall (_, _, _, e) ->
	  gen e
      | ObjLit _ -> IdSet.empty
      | LabelLit (_, l) ->
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

  (* Compute life variable information for a statement.  The parameters
     [may] and [must] are the output set of all successors.  The parameter
     [stmt] is the current statement we analyse.  The statement's note will
     be updated with the variables life on the input edge. *)

  let rec compute_in_statement may must stmt =
    match stmt with
	Skip n ->
	  let n' = { n with may_live = may; must_live = must } in
	    logio stmt may n'.may_live ;
	    Skip n'
      | Assert (n, e) ->
	  let g = gen e in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Assert (n', e)
      | Prove (n, e) ->
	  let g = gen e in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Prove (n', e)
      | Assign (n, lhs, rhs) ->
	  let k = List.fold_left (add kill) IdSet.empty lhs
	  and g = List.fold_left (add gen) IdSet.empty rhs in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    Assign (n', lhs, rhs)
      | Await (n, c) ->
	  let g = gen c in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Await (n', c)
      | Posit (n, c) ->
	  let g = gen c in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Posit (n', c)
      | Release n ->
	  let n' = { n with may_live = may; must_live = must }
	  in
	    logio stmt may n'.may_live ;
	    Release n'
      | AsyncCall (n, None, c, m, s, a) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::a) in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    AsyncCall (n', None, c, m, s, a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::a)
	  and k =  kill l in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    AsyncCall (n', Some l, c, m, s, a)
      | Get (n, l, p) ->
	  let g = gen l in
	  let k = List.fold_left (add kill) IdSet.empty p in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    Get (n', l, p)
      | Free (n, v) ->
	  (* This statement keeps its arguments life, even though the
	     list of variables here is to be released. The call to [kill]
	     is used for typing reasons only. *)
	  let g = List.fold_left (add kill) IdSet.empty v in
	  let n' = { n with may_live = IdSet.union may g;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Free (n', v)
      | Bury (n, v) ->
	  (* This statement must not affect the life range of any value,
	     and all its arguments must be dead at that point. *)
	  let k = List.fold_left (add kill) IdSet.empty v in
	  let n' = { n with may_live = IdSet.diff may k;
			    must_live = IdSet.diff must k }
	  in
	    logio stmt may n'.may_live ;
	    Bury (n', v)
      | SyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::i)
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    SyncCall (n', c, m, s, i, o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::i)
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    AwaitSyncCall (n', c, m, s, i, o)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  let g = List.fold_left (add gen) IdSet.empty i in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    LocalAsyncCall (n', None, m, s, ub, lb, i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  let g = List.fold_left (add gen) IdSet.empty i
	  and k = kill l in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    LocalAsyncCall (n', Some l, m, s, ub, lb, i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty i
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    LocalSyncCall (n', m, s, u, l, i, o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty i
	  and k = List.fold_left (add kill) IdSet.empty o in
	  let n' = { n with may_live = IdSet.union g (IdSet.diff may k);
			    must_live = IdSet.union g (IdSet.diff must k) }
	  in
	    logio stmt may n'.may_live ;
	    AwaitLocalSyncCall (n', m, s, u, l, i, o)
      | MultiCast (n, c, m, s, a) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::a) in
	  let n' = { n with may_live = IdSet.union g may } in
	    logio stmt may n'.may_live ;
	    MultiCast (n', c, m, s, a)
      | Tailcall (n, c, m, s, i) ->
	  let g = List.fold_left (add gen) IdSet.empty (c::i) in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Tailcall (n', c, m, s, i)
      | StaticTail (n, m, s, u, l, ins) ->
	  let g = List.fold_left (add gen) IdSet.empty ins in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    StaticTail (n', m, s, u, l, ins)
      | Return (n, el) ->
	  let g = List.fold_left (add gen) IdSet.empty el in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
          in
	    logio stmt may n'.may_live ;
            Return (n', el)
      | If (n, c, l, r) ->
	  let l' = compute_in_statement may must l
	  and r' = compute_in_statement may must r in
	  let g = gen c in
	  let n' = { n with may_live =  IdSet.union g (IdSet.union (note l').may_live (note r').may_live);
			    must_live = IdSet.union g (IdSet.inter (note l').must_live (note r').must_live) }
	  in
	    logio stmt may n'.may_live ;
	    If (n', c, l', r')
      | While (n, c, i, b) ->
	  let b' = compute_in_statement may must b in
	  let g = IdSet.union (gen c) (gen i)
	  in
	  let n' = { n with may_live = IdSet.union g ((note b').may_live);
			    must_live = IdSet.union g ((note b').must_live) }
	  in
	    logio stmt may n'.may_live ;
	    While (n', c, i, b')
      | DoWhile (n, c, i, b) ->
	  let b' = compute_in_statement may must b in
	  let g = IdSet.union (gen c) (gen i)
	  in
	  let n' = { n with may_live = IdSet.union g ((note b').may_live);
			    must_live = IdSet.union g ((note b').must_live) }
	  in
	    logio stmt may n'.may_live ;
	    DoWhile (n', c, i, b')
      | Sequence (n, s1, s2) ->
	  let s2' = compute_in_statement may must s2 in
	  let s1' = compute_in_statement (note s2').may_live (note s2').must_live s1 in
	    (* the out of the statement is the out of the first statement. *)
	  let n' = { n with may_live = (note s1').may_live;
			    must_live = (note s1').must_live }
	  in
	    logio stmt may n'.may_live ;
	    Sequence (n', s1', s2')
      | Merge _ -> assert false
      | Choice (n, s1, s2) -> 
	  let s1' = compute_in_statement may must s1
	  and s2' = compute_in_statement may must s2 in
	  let n' = { n with may_live = IdSet.union (note s1').may_live (note s2').may_live;
			    must_live = IdSet.inter (note s1').must_live (note s2').must_live }
	  in
	    logio stmt may n'.may_live ;
	    Choice (n', s1', s2')
      | Continue (n, e) ->
	  let g = gen e in
	  let n' = { n with may_live = IdSet.union g may;
			    must_live = IdSet.union g must }
	  in
	    logio stmt may n'.may_live ;
	    Continue (n', e)
      | Extern (n, s) ->
	  let n' = { n with may_live = may } in
	    logio stmt may n'.may_live ;
	    Extern (n', s)
  in
    match meth.Method.body with
	None -> meth
      | Some b ->
	  let () = log 1 ("Live vars in " ^ (Method.name_as_string meth)) in
	  let add s v = IdSet.add v.VarDecl.name s in
	  let outs = List.fold_left add IdSet.empty meth.Method.outpars in
	    (* The set of output variables may and must live. *)
	    { meth with Method.body = Some (compute_in_statement outs outs b) }


let compute_in_method program cls meth =
  let () = Messages.message 2
    ("Compute life ranges in " ^ cls.Class.name ^ "::" ^ meth.Method.name)
  in
    match meth.Method.body with
	None -> meth
      | Some b -> compute_in_body program cls meth


(* Compute life ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let analyse program = Program.for_each_method program compute_in_method
