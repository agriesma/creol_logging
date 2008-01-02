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

let log l = Messages.message (l + 1)

(* This function inserts free statements for all label variables at
   the point at which they die. *)

let optimize prg =
  let optimise_in_statement meth stmt =

    (* Decide whether we should append a free statement to the current
       statement.  If no free statement needs to be appended, then the
       function returns [s].  Otherwise, a Sequence statement will be
       returned, which has a \emph{different} defined set than the
       original statement.  This means, that we have to update all
       subsequent defined sets.  *)

    let append_free ~s ~l =
      let d = def s in
      let r =
	IdSet.filter
	  (fun v -> Method.label_p meth v)
	  (IdSet.diff d l)
      in
	if IdSet.is_empty r then
	  let () = log 0 ((file s) ^ ": " ^ (string_of_int (line s)) ^
			    ": [" ^ (Statement.to_string s) ^
			    "] d = " ^ (string_of_idset d) ^
			    "; l = " ^ (string_of_idset l) ^
			    "; r = {}")
	  in
	    s
	else
	  let d' = IdSet.diff d r in
	  let () = log 0 ((file s) ^ ": " ^ (string_of_int (line s)) ^
			    ": [" ^ (Statement.to_string s) ^
			    "] d = " ^ (string_of_idset d) ^
			    "; l = " ^ (string_of_idset l) ^
			    "; r = " ^ (string_of_idset r) ^
			    "; d' = " ^ (string_of_idset d')) in
	  let r' =
	    IdSet.fold
	      (fun e a -> LhsId (Expression.make_note (), e) :: a)
	      r []
	  in
	  let n = {(note s) with def = d' } in
	    Sequence (n, s, Free (n, r'))
    in

    (* Insert free statements.  [lv] is a set of label names which are
       life at a given location. *)

    let rec work lv =
      function
	| If (n, c, s1, s2) ->
	    let s1' = work lv s1
	    and s2' = work lv s2 in
	    let def' = IdSet.inter (def s1') (def s2') in
	      append_free (If ({n with def = def' }, c, s1', s2')) lv
	| While (n, c, i, s) ->
	    let s' = append_free (work lv s) lv in
	      append_free (While ({ n with def = def s' }, c, i, s')) lv
	| Sequence (n, s1, s2) ->
	    let s1' = work (life s2) s1 in
	    let s2' = TreeDef.compute_in_statement meth (def s1') s2 in
	    let s2'' = work lv s2' in
	      Sequence ({ n with def = def s2'' }, s1', s2'')
	| Choice (n, s1, s2) ->
	    let s1' = work lv s1
	    and s2' = work lv s2 in
	    let def' = IdSet.inter (def s1') (def s2') in
	      Choice ({ n with def = def' }, s1', s2')
	| Merge (n, s1, s2) ->
	    let s1' = work lv s1
	    and s2' = work lv s2 in
	    let def' = IdSet.inter (def s1') (def s2') in
	      Merge ({ n with def = def' }, s1', s2')
	| s -> append_free s lv
    in
    let lv =
      let add a { VarDecl.name = n } = IdSet.add n a in
	List.fold_left add IdSet.empty meth.Method.outpars
    in
      work lv stmt
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
