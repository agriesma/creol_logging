(*
 * TreeBury.ml -- Bury dead variables.
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

(*s Bury all variables holding dead values.

  Requires life ranges and defined ranges. *)

open Creol
open Expression
open Statement
open VarDecl

let log l = Messages.message (l + 1)

(* This function inserts bury statements for all variables at the
   point at which they die.

   \textbf{TO DO:} This function will often insert redundant bury
   statements.  The user may write \lstinline!v := null! and never
   read from \lstinline!v! thereafter.  Then \lstinline!v! is declared
   to be dead and a [Bury] node is generated, causing an additional
   \lstinline!v := null! in the output. *)

let optimise_in_statement meth stmt =

  (* Decide whether we should append a \textbf{bury} statement to
     the current statement.  If no \textbf{bury} statement needs to
     be appended, then the function returns [s].  The parameter [l]
     contains the set of variables which are life \emph{after}
     executing that statement.  Otherwise, a Sequence statement will
     be returned, which has a \emph{different} defined set than the
     original statement.  This means, that all subsequent defined
     sets have to be updated.  *)

  let append_bury ~s ~l =
    let d = def s in
    let r =
      IdSet.filter
	(fun v -> not (Method.label_p meth v) && not (Method.input_p meth v))
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
	  Sequence (n, s, Bury (n, r'))
  in
  let rec work lv =
    function
      | If (n, c, s1, s2) ->
	  let s1' = work lv s1
	  and s2' = work lv s2 in
	  let def' = IdSet.inter (def s1') (def s2') in
	    append_bury (If ({n with def = def' }, c, s1', s2')) lv
      | While (n, c, i, s) ->
	  let s' = append_bury (work lv s) lv in
	    append_bury (While ({ n with def = def s' }, c, i, s')) lv
      | DoWhile (n, c, i, s) ->
	  let s' = append_bury (work lv s) lv in
	    append_bury (DoWhile ({ n with def = def s' }, c, i, s')) lv
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
      | s -> append_bury s lv
  in
  let lv =
    let add a { VarDecl.name = n } = IdSet.add n a in
      List.fold_left add IdSet.empty meth.Method.outpars
  in
    work lv stmt


let optimise_in_method prg cls meth =
  match meth.Method.body with
      None ->
	meth
    | Some body ->
	{ meth with Method.body = Some (optimise_in_statement meth body) }

let optimize prg = Program.for_each_method prg optimise_in_method
