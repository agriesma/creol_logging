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
      log 1 ("Defined at " ^ w ^ " [" ^ (Statement.to_string  stmt) ^
	       "]: in = {" ^ (g i) ^ "}, out = {" ^ (g o) ^ "}")


(* Compute the defined ranges in a statement. *)

let compute_in_statement ~meth ins stmt =
  let rec kill =
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
	  List.fold_left (add kill) IdSet.empty l
      | ListLit (a, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | SetLit (a, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Unary (a, o, e) ->
	  kill e
      | Binary (a, o, l, r) ->
	  IdSet.union (kill l) (kill r)
      | Expression.If (a, c, t, f) ->
	  List.fold_left (add kill) IdSet.empty [c; t; f]
      | FuncCall (a, f, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Expression.Label (a, l) ->
	  kill l
      | New (a, c, l) ->
	  List.fold_left (add kill) IdSet.empty l
      | Expression.Extern _ ->
	  IdSet.empty
      | SSAId (a, v, n) ->
	  assert (Method.local_p meth v); IdSet.singleton v
      | Phi (a, l) ->
	  List.fold_left (add kill) IdSet.empty l
  in
  let gen =
    function
	LhsId (n, i) when Method.local_p meth i -> IdSet.singleton i
      | LhsId (n, i) -> IdSet.empty
      | LhsAttr (n, s, t) -> IdSet.empty
      | LhsWildcard (n, t) -> IdSet.empty
      | LhsSSAId (n, i, v) ->
	  assert (Method.local_p meth i); IdSet.singleton i
  in
  let rec work ins stmt =
    match stmt with
	Skip n ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Skip n'
      | Assert (n, e) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Assert (n', e)
      | Prove (n, e) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Prove (n', e)
      | Assign (n, lhs, rhs) ->
	  let g = List.fold_left (add gen) IdSet.empty lhs in
	  let n' = { n with def = IdSet.union g ins } in
	    logio stmt ins n'.def ;
	    Assign (n', lhs, rhs)
      | Await (n, c) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Await (n', c)
      | Posit (n, c) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Posit (n', c)
      | Release n ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Release n'
      | AsyncCall (n, None, c, m, s, a) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    AsyncCall (n', None, c, m, s, a)
      | AsyncCall (n, Some l, c, m, s, a) ->
	  let g =  gen l in
	  let n' = { n with def = IdSet.union ins g } in
	    logio stmt ins n'.def ;
	    AsyncCall (n', Some l, c, m, s, a)
      | Reply (n, l, p) ->
	  (* A reply statement leaves [l] undefined and defines [p]. *)
	  let k = kill l
	  and g = List.fold_left (add gen) IdSet.empty p in
	  let n' = { n with def = IdSet.union (IdSet.diff ins k) g } in
	    logio stmt ins n'.def ;
	    Reply (n', l, p)
      | Free (n, v) ->
	  (* A free statement will leave all members of v as
	     undefined.  The call to the gen-function is used only for
	     typing reasons in OCaml. *)
	  let k = List.fold_left (add gen) IdSet.empty v in
	  let n' = { n with def = IdSet.diff ins k } in
	    logio stmt ins n'.def ;
	    Free (n', v)
      | Bury (n, v) ->
	  (* A bury statement will leave all members of v as
	     undefined.  The call to the gen-function is used only for
	     typing reasons in OCaml. *)
	  let k = List.fold_left (add gen) IdSet.empty v in
	  let n' = { n with def = IdSet.diff ins k } in
	    logio stmt ins n'.def ;
	    Bury (n', v)
      | SyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with def = IdSet.union ins g } in
	    logio stmt ins n'.def ;
	    SyncCall (n', c, m, s, i, o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with def = IdSet.union ins g } in
	    logio stmt ins n'.def ;
	    AwaitSyncCall (n', c, m, s, i, o)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    LocalAsyncCall (n', None, m, s, ub, lb, i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  let g = gen l in
	  let n' = { n with def = IdSet.union ins g } in
	    logio stmt ins n'.def ;
	    LocalAsyncCall (n', Some l, m, s, ub, lb, i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with def = IdSet.union ins g }
	  in
	    logio stmt ins n'.def ;
	    LocalSyncCall (n', m, s, u, l, i, o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  let g = List.fold_left (add gen) IdSet.empty o in
	  let n' = { n with def = IdSet.union g ins } in
	    logio stmt ins n'.def ;
	    AwaitLocalSyncCall (n', m, s, u, l, i, o)
      | Tailcall (n, m, s, ub, lb, i) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Tailcall (n', m, s, ub, lb, i)
      | If (n, c, l, r) ->
	  let l' = work ins l
	  and r' = work ins r in
	  let n' = { n with def = IdSet.inter (def l') (def r') }
	  in
	    logio stmt ins n'.def ;
	    If (n', c, l', r')
      | While (n, c, i, b) ->
	  let b' = work ins b in
	  let n' = { n with def = IdSet.union ins (def b') } in
	    logio stmt ins n'.def ;
	    While (n', c, i, b')
      | Sequence (n, s1, s2) ->
	  let s1' = work ins s1 in
	  let s2' = work (def s1') s2 in
	  let n' = { n with def = def s2' } in
	    logio stmt ins n'.def ;
	    Sequence (n', s1', s2')
      | Merge (n, s1, s2) -> 
	  let s1' = work ins s1
	  and s2' = work ins s2 in
	  let n' = { n with def = IdSet.inter (def s1') (def s2') } in
	    logio stmt ins n'.def ;
	    Merge (n', s1', s2')
      | Choice (n, s1, s2) -> 
	  let s1' = work ins s1
	  and s2' = work ins s2 in
	  let n' = { n with def = IdSet.inter (def s1') (def s2') } in
	    logio stmt ins n'.def ;
	    Choice (n', s1', s2')
      | Extern (n, s) ->
	  let n' = { n with def = ins } in
	    logio stmt ins n'.def ;
	    Extern (n', s)
  in
    work ins stmt

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
	  { meth with Method.body = Some (compute_in_statement meth ins b) }


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
