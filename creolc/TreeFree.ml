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
	    let free' = IdSet.remove (name l) free in
	      (free', set_freed s free')
	| LocalAsyncCall (_, Some l, _, _, _, _, _) as s ->
	    let free' = IdSet.remove (name l) free in
	      (free', set_freed s free')
	| Reply (n, l, v) ->
	    let free' =
	      let nm = variable l in
	        Messages.message 1
		  ("Variable " ^ nm ^ " freed (consumed) at " ^ (file n) ^
		    ": " ^ (string_of_int (line n)));
		  IdSet.add nm free
	    in
	      (free', Reply ({ n with freed = free'}, l, v))
	| Free (n, l) ->
	    let f a e =
	      let nm = name e in
	        Messages.message 1
		  ("Variable " ^ nm ^ " freed at " ^ (file n) ^ ": " ^
		    (string_of_int (line n)));
		IdSet.add nm a
	    in
	    let free' = List.fold_left f free l in
	      (free', Free ({ n with freed = free'}, l))
	| If (n, c, s1, s2) ->
	    let (free', s1') = work free s1 in
	    let (free'', s2') = work free' s2 in
	      (*i assert (IdSet.equal free' free''); i*)
	      (free'', If ({n with freed = free'' }, c, s1', s2'))
	| While (n, c, i, s) ->
	    let (free', s') = work free s in
	      (free', While ({ n with freed = free' }, c, i, s'))
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
		(free'', Sequence ({ n with freed = free'' }, s1', s2'))
	      else
		let k' =
		  let f e a =
		    Messages.message 1
		      ("Freeing " ^ e ^ " at " ^ (file (note s2)) ^ ": " ^
			(string_of_int (line (note s2)))) ;
		    (LhsId (Expression.make_note (), e))::a
		  in
		    IdSet.fold f k []
		in
		  (IdSet.diff free'' k, Sequence ({ n with freed = free'' }, s1',
			       Sequence (note s2, Free (note s2, k'), s2')))
	| Choice (n, s1, s2) ->
	    let (f1, s1') = work free s1 and (f2, s2') = work free s2 in
            let free' = IdSet.union f1 f2 in
	      (*i assert (IdSet.equal f1 f2) ; i*)
	      (free', Choice ({ n with freed = free' }, s1', s2'))
	| Merge (n, s1, s2) ->
	    let (f1, s1') = work free s1 and (f2, s2') = work free s2 in
	    let free' = IdSet.union f1 f2 in
	      (*i assert (IdSet.equal f1 f2) ; i*)
	      (free', Merge ({ n with freed = free' }, s1', s2'))
	| s -> (free, set_freed s free)
    in
    let (free', body') = work IdSet.empty stmt in
      (*i assert (IdSet.is_empty free'); i*) body'
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
