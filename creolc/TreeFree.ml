(*
 * TreeFree.ml -- Free dead labels.
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

(*s Free all labels which are not read from.

  Requires life ranges. *)

open Creol
open Expression
open Statement
open VarDecl
open Method

(* This function inserts free statements for all label variables at
   the point at which they die. *)

let optimize prg =
  let optimise_in_statement meth stmt =
    let name =
      function
	  LhsId (_, v) -> v
	| LhsSSAId (_, v, _) -> v
	| _ -> assert false
    in
    let rec work free =
      function
	| AsyncCall (_, Some l, _, _, _, _) as s ->
	    (IdSet.remove (name l) free, s)
	| LocalAsyncCall (_, Some l, _, _, _, _, _) as s ->
	    (IdSet.remove (name l) free, s)
	| Free (_, l) as s ->
	    (List.fold_left (fun a e -> IdSet.add (name e) a) free l, s)
	| If (n, c, s1, s2) ->
	    let (free', s1') = work free s1 in
	    let (free'', s2') = work free' s2 in
	      assert (IdSet.equal free' free''); (free'', If (n, c, s1', s2'))
	| While (n, c, i, s) ->
	    let (free', s') = work free s in
	      (free', While (n, c, i, s'))
	| Sequence (n, s1, s2) ->
	    let (free', s1') = work free s1 in
	    let (free'', s2') = work free' s2 in
	    let k =
	      IdSet.filter
		(fun v -> not (IdSet.mem v free') &&
		  Type.label_p (find_variable meth v).var_type)
		(IdSet.diff (life s1) (life s2))
	    in
	      if IdSet.is_empty k then
		(free'', Sequence (n, s1', s2'))
	      else
		let k' =
		  IdSet.fold
		    (fun e a -> (LhsId (Expression.dummy_note, e))::a)
		    k []
		in
		  (IdSet.diff free'' k, Sequence (n, s1',
			       Sequence (note s2, Free (note s2, k'), s2')))
	| Choice (n, s1, s2) ->
	    let (f1, s1') = work free s1
	    and (f2, s2') = work free s2
	    in
	      assert (IdSet.equal f1 f2) ; (f2, Choice (n, s1', s2'))
	| Merge (n, s1, s2) ->
	    let (f1, s1') = work free s1
	    and (f2, s2') = work free s2
	    in
	      assert (IdSet.equal f1 f2) ; (f2, Merge (n, s1', s2'))
	| s -> (free, s)
    in
    let (free', body') = work IdSet.empty stmt in
      assert (IdSet.is_empty free'); body'
  in
  let optimise_in_method meth =
    match meth.Method.body with
	None ->
	  meth
      | Some body ->
	  let body' = optimise_in_statement meth body in
	    { meth with Method.body = Some body' }
  in
  let optimise_in_with w =
    { w with With.methods = List.map optimise_in_method w.With.methods }
  in
  let optimise_in_class c =
    { c with Class.with_defs = List.map optimise_in_with c.Class.with_defs }
  in
  let optimise_declaration =
    function
	Declaration.Class c -> Declaration.Class (optimise_in_class c)
      | d -> d
  in
    List.map optimise_declaration prg
