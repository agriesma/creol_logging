(*
 * TreeDef.ml -- Tree-based defined variable analysis for Creol programs
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

(*s Compute definition ranges of variables in Creol programs.

  A variable is called \emph{defined} at a statement $s$, if it has
  been written to on all paths leading to that statement.
  This can be computed with the data-flow equation
  \begin{equation*}
    \mathit{defs}_{\mathit{out}}(s)= \mathit{gen}(s)\cap
    (\mathit{defs}_{\mathit{in}}(s)\setminus \mathit{kill}(s))\quad,
  \end{equation*}
  where $\mathit{defs}_{\mathit{in}}(s)=
  \bigcap_{p\in\mathit{pred}(s)}\mathit{defs}_{\mathit{out}}(p)$.  The set 
  $\mathit{defs}_{\mathit{in}}(\mathit{init})$ is equal to the
  in-parameters of the method (these are always defined in a method).

  The function [gen] computes the set of variables \emph{written} in
  a statement, which usually happens only by expressions.  The function
  [kill] defines the set of variables which will be \emph{undefined}
  after that statement.  This set is usually empty, except for
  \emph{bury} and \emph{free} statements.
*)

open Creol
open Expression
open Statement


(* Log messages for definedness analysis *)
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
      log 1 ("Defined at " ^ w ^ " [" ^ (Statement.to_string  stmt) ^
	       "]: in = {" ^ (g i) ^ "}, out = {" ^ (g o) ^ "}")


(* Compute the defined ranges in a statement. *)

let compute_in_statement ~meth may must stmt =
  let rec kill =
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
	     Bool _ | Int _ | Float _ | String _ | History _) -> IdSet.empty
      | Id (_, v)  ->
	  if Method.local_p meth v then IdSet.singleton v else IdSet.empty
      | StaticAttr _ ->
	  IdSet.empty
      | Tuple (_, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | ListLit (_, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | SetLit (_, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Unary (_, _, e) ->
	  kill e
      | Binary (_, _, l, r) ->
	  IdSet.union (kill l) (kill r)
      | Expression.If (_, c, t, f) ->
	  List.fold_left (add kill) IdSet.empty [c; t; f]
      | FuncCall (_, _, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Expression.Label (_, l) ->
	  kill l
      | New (_, _, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Choose (_, _, _, e) | Exists (_, _, _, e) | Forall (_, _, _, e) ->
	  kill e
      | ObjLit _ ->
	  IdSet.empty
      | LabelLit (_, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Expression.Extern _ ->
	  IdSet.empty
      | SSAId (_, v, _) ->
	  assert (Method.local_p meth v); IdSet.singleton v
      | Phi (_, l) ->
	  List.fold_left (add kill) IdSet.empty l
  in
  let gen =
    function
	LhsId (_, i) when Method.local_p meth i -> IdSet.singleton i
      | LhsId (_, i) -> IdSet.empty
      | LhsAttr (_, _, _) -> IdSet.empty
      | LhsWildcard (_, _) -> IdSet.empty
      | LhsSSAId (_, i, _) ->
	  assert (Method.local_p meth i); IdSet.singleton i
  in
  let rec work may must stmt =
    match stmt with
	Skip n ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Skip n'
      | Assert (n, e) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Assert (n', e)
      | Prove (n, e) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Prove (n', e)
      | Assign (n, lhs, rhs) ->
	  let g = List.fold_left (add gen) IdSet.empty lhs in
	  let n' = { n with may_def = IdSet.union g may;
			    must_def = IdSet.union g must } in
	    logio stmt must n'.must_def ;
	    Assign (n', lhs, rhs)
      | Await (n, c) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Await (n', c)
      | Posit (n, c) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Posit (n', c)
      | Release n ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Release n'
      | AsyncCall (n, None, c, m, s, a) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    AsyncCall (n', None, c, m, s, a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let g =  gen l in
	  let n' = { n with may_def = IdSet.union may g;
			    must_def = IdSet.union must g } in
	    logio stmt must n'.must_def ;
	    AsyncCall (n', Some l, c, m, s, a)
      | Get (n, l, p) ->
	  (* A reply statement leaves [l] undefined and defines [p]. *)
	  let k = kill l
	  and g = List.fold_left (add gen) IdSet.empty p in
	  let n' = { n with may_def = IdSet.union (IdSet.diff may k) g;
			    must_def = IdSet.union (IdSet.diff must k) g } in
	    logio stmt must n'.must_def ;
	    Get (n', l, p)
      | Free (n, v) ->
	  (* A free statement will leave all members of v as
	     undefined.  The call to the gen-function is used only for
	     typing reasons in OCaml. *)
	  let k = List.fold_left (add gen) IdSet.empty v in
	  let n' = { n with may_def = IdSet.diff may k;
			    must_def = IdSet.diff must k } in
	    logio stmt must n'.must_def ;
	    Free (n', v)
      | Bury (n, v) ->
	  (* A bury statement will leave all members of v as
	     undefined.  The call to the gen-function is used only for
	     typing reasons in OCaml. *)
	  let k = List.fold_left (add gen) IdSet.empty v in
	  let n' = { n with may_def = IdSet.diff may k;
			    must_def = IdSet.diff must k } in
	    logio stmt must n'.must_def ;
	    Bury (n', v)
      | SyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with may_def = IdSet.union may g;
			    must_def = IdSet.union must g } in
	    logio stmt must n'.must_def ;
	    SyncCall (n', c, m, s, i, o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with may_def = IdSet.union may g;
			    must_def = IdSet.union must g } in
	    logio stmt must n'.must_def ;
	    AwaitSyncCall (n', c, m, s, i, o)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    LocalAsyncCall (n', None, m, s, ub, lb, i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  let g = gen l in
	  let n' = { n with may_def = IdSet.union may g;
			    must_def = IdSet.union must g } in
	    logio stmt must n'.must_def ;
	    LocalAsyncCall (n', Some l, m, s, ub, lb, i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with may_def = IdSet.union may g;
			    must_def = IdSet.union must g }
	  in
	    logio stmt must n'.must_def ;
	    LocalSyncCall (n', m, s, u, l, i, o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with may_def = IdSet.union may g;
			    must_def = IdSet.union must g } in
	    logio stmt must n'.must_def ;
	    AwaitLocalSyncCall (n', m, s, u, l, i, o)
      | MultiCast (n, c, m, s, i) ->
	  let a' = { n with may_def = may; must_def = must } in
	    logio stmt must a'.must_def ;
	    MultiCast (a', c, m, s, i)
      | Tailcall (n, c, m, s, i) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Tailcall (n', c, m, s, i)
      | StaticTail (n, m, s, ub, lb, i) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    StaticTail (n', m, s, ub, lb, i)
      | Return (n, el) ->
	  let n' = { n with may_def = may; must_def = must } in
	    Return (n', el)
      | If (n, c, l, r) ->
	  let l' = work may must l
	  and r' = work may must r in
	  let n' = { n with may_def = IdSet.union (note l').may_def (note r').may_def;
			    must_def = IdSet.inter (note l').must_def (note r').must_def }
	  in
	    logio stmt must n'.must_def ;
	    If (n', c, l', r')
      | While (n, c, i, b) ->
	  let b' = work may must b in
	  let n' = { n with may_def = IdSet.union may (note b').may_def;
			    must_def = IdSet.union must (note b').must_def }
	  in
	    logio stmt must n'.must_def ;
	    While (n', c, i, b')
      | DoWhile (n, c, i, b) ->
	  let b' = work may must b in
	  let n' = { n with may_def = IdSet.union may (note b').may_def;
			    must_def = IdSet.union must (note b').must_def }
	  in
	    logio stmt must n'.must_def ;
	    DoWhile (n', c, i, b')
      | Sequence (n, s1, s2) ->
	  let omay = (note s1).may_def
          and omust = (note s1).must_def in
	  let s1' = work may must s1 in
	  let may' = (note s1').may_def
          and must' = (note s1').must_def in
	  if not ((IdSet.equal omay may') && (IdSet.equal omust must')) then
	    (* The may and must set changed, and therefore, the
	       information in [s2] needs updating.  Recurse into [s2]
	       to update the chain. *)
            begin
	      let s2' = work may' must' s2 in
	      let n' = { n with may_def = (note s2').may_def;
			        must_def = (note s2').must_def } in
	        logio stmt must n'.must_def ;
	        Sequence (n', s1', s2')
            end
	  else
	    (* The may and must set did not change, and therefore, the
	       information in [s2] is up to date.  We can stop working
	       through the chain. *)
	    Sequence(n, s1, s2)
      | Merge _ -> assert false
      | Choice (n, s1, s2) -> 
	  let s1' = work may must s1
	  and s2' = work may must s2 in
	  let n' = { n with  may_def = IdSet.union (note s1').may_def (note s2').may_def;
			     must_def = IdSet.inter (note s1').must_def (note s2').must_def } in
	    logio stmt must n'.must_def ;
	    Choice (n', s1', s2')
      | Continue (n, e) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Continue (n', e)
      | Extern (n, s) ->
	  let n' = { n with may_def = may; must_def = must } in
	    logio stmt must n'.must_def ;
	    Extern (n', s)
  in
    work may must stmt

(* Compute defined ranges of a method body by traversing it forward. *)

let compute_in_body ~program ~cls ~meth =

  (* Check whether an expression defines a new value.  This will
     almost never happen.  The note is updated with the set of defined
     variables of the output edge. *)

  match meth.Method.body with
      None -> meth
    | Some b ->
	let () = log 1 ("Defined vars in " ^ (Method.name_as_string meth)) in
	let add s v = IdSet.add v.VarDecl.name s in
	let ins = List.fold_left add IdSet.empty meth.Method.inpars in
	  { meth with Method.body = Some (compute_in_statement meth ins ins b) }


let compute_in_method program cls meth =
  let () = log 2
    ("Compute defined ranges in " ^ cls.Class.name ^ "::" ^ meth.Method.name)
  in
    match meth.Method.body with
	None -> meth
      | Some b -> compute_in_body program cls meth


(* Compute defined ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let analyse program = Program.for_each_method program compute_in_method 
