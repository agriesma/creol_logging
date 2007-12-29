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

    (* Decide whether we should append a free statement to the current
       statement. *)

    let append_free s =
      let d = def s and l = life s and f = freed s in
      let r =
	IdSet.filter
	  (fun v -> Type.label_p (find_variable meth v).var_type)
	  (IdSet.diff d (IdSet.union l f))
      in
	Messages.message 1 ((file s) ^ ": " ^ (string_of_int (line s)) ^
			      ": d = " ^ (string_of_idset d) ^
			      "; l = " ^ (string_of_idset l) ^
			      "; r = " ^ (string_of_idset r)) ;
	if IdSet.is_empty r then
	  s
	else
	  let r' =
	    IdSet.fold
	      (fun e a -> LhsId (Expression.make_note (), e) :: a)
	      r []
	  in
	  let n = {(note s) with freed = IdSet.union (freed s) r} in
	    assert (IdSet.is_empty (IdSet.inter f r));
	    assert (r' <> []) ;
	    Sequence (n, s, Free (n, r'))
    in

    (* Insert free statements.  [free] is a set of label names which are
       known to be consumed at a specific statement. *)

    let rec work free =
      function
	| AsyncCall (_, Some l, _, _, _, _) as s ->
	    let free' = IdSet.remove (name l) free in
	      append_free (set_freed s free')
	| LocalAsyncCall (_, Some l, _, _, _, _, _) as s ->
	    let free' = IdSet.remove (name l) free in
	      append_free (set_freed s free')
	| Reply (n, l, v) ->
	    let free' =
	      let nm = variable l in
	        Messages.message 1
		  ("Variable " ^ nm ^ " freed (consumed) at " ^ (n.file) ^
		     ": " ^ (string_of_int (n.line)));
		IdSet.add nm free
	    in
	      append_free (Reply ({ n with freed = free'}, l, v))
	| Free (n, l) ->
	    let f a e =
	      let nm = name e in
	        Messages.message 1
		  ("Variable " ^ nm ^ " freed at " ^ (n.file) ^ ": " ^
		     (string_of_int (n.line)));
		IdSet.add nm a
	    in
	    let free' = List.fold_left f free l in
	      Free ({ n with freed = free'}, l)
	| If (n, c, s1, s2) ->
	    let s1' = work free s1 in
	    let s2' = work free s2 in
	      assert (IdSet.equal (freed s1') (freed s2')) ;
	      append_free (If ({n with freed = (freed s2') }, c, s1', s2'))
	| While (n, c, i, s) ->
	    let s' = append_free (work free s) in
	      append_free (While ({ n with freed = freed s' }, c, i, s'))
	| Sequence (n, s1, s2) ->
	    let s1' = work free s1 in
	    let s2' = work (freed s1') s2 in
	      append_free (Sequence ({ n with freed = freed s2' }, s1', s2'))
	| Choice (n, s1, s2) ->
	    let s1' = work free s1
	    and s2' = work free s2 in
	      assert (IdSet.equal (freed s1') (freed s2')) ;
	      append_free (Choice ({ n with freed = freed s2' }, s1', s2'))
	| Merge (n, s1, s2) ->
	    let s1' = work free s1
	    and s2' = work free s2 in
	      assert (IdSet.equal (freed s1') (freed s2')) ;
	      append_free (Merge ({ n with freed = freed s2' }, s1', s2'))
	| s -> append_free s
    in
      append_free (work IdSet.empty stmt)
  in
  let optimise_in_method meth =
    match meth.Method.body with
	None ->
	  meth
      | Some body ->
	  let body' =
	    optimise_in_statement meth
	      (Sequence (make_note (), body, Skip (make_note ())))
	  in
	    { meth with Method.body = Some (remove_redundant_skips body') }
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
