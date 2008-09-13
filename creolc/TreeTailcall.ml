(*
 * TreeTailcall.ml -- Optimize tailcalls.
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

(*s

*)

open Creol
open Expression
open Statement

let tailcall_counter = ref 0

let tailcall_successes () = !tailcall_counter

let optimise_in_statement outs stmt =
  let fits_p out expr =
    match expr with
      | LhsId (_, n) | LhsSSAId (_, n, _) when n = out -> true
      | _ -> false
  and matches_p out expr =
    match expr with
      | Id (_, n) | SSAId (_, n, _) when n = out -> true
      | _ -> false
  and equals_p out expr =
    match (out, expr) with
      | (LhsId(_, n), Id(_, n'))
      | (LhsSSAId(_, n, _), Id(_, n'))
      | (LhsId(_, n), SSAId(_, n', _)) -> n = n'
      | (LhsSSAId(_, n, i), SSAId(_, n', i')) -> n = n' && i = i'
      | _ -> false
  in
  let rec work =
    function
      | Sequence (n, SyncCall (_, c, m, s, i, o), Return (_, r)) when
	      ((List.length outs) = (List.length o)) &&
	      ((List.length outs) = (List.length r)) &&
	      (List.for_all2 fits_p outs o) &&
	      (List.for_all2 matches_p outs r) ->
	  Tailcall (n, c, m, s, i)
      | Sequence (n, AsyncCall (_, Some l, c, m, s, i),
	  Sequence (_, Reply(_, l', o), Return (_, r))) when
	      (equals_p l l') &&
	      ((List.length outs) = (List.length o)) &&
	      ((List.length outs) = (List.length r)) &&
	      (List.for_all2 fits_p outs o) &&
	      (List.for_all2 matches_p outs r) ->
	  Tailcall (n, c, m, s, i)
      | Sequence (n, LocalSyncCall (_, m, s, lb, ub, i, o), Return (_, r)) when
	      ((List.length outs) = (List.length o)) &&
	      ((List.length outs) = (List.length r)) &&
	      (List.for_all2 fits_p outs o) &&
	      (List.for_all2 matches_p outs r) ->
	  StaticTail (n, m, s, lb, ub, i)
      | Sequence (n, LocalAsyncCall (_, Some l, m, s, lb, ub, i),
	  Sequence (_, Reply(_, l', o), Return (_, r))) when
	      (equals_p l l') &&
	      ((List.length outs) = (List.length o)) &&
	      ((List.length outs) = (List.length r)) &&
	      (List.for_all2 fits_p outs o) &&
	      (List.for_all2 matches_p outs r) ->
	  StaticTail (n, m, s, lb, ub, i)
      | If (n, c, s1, s2) ->
	  If (n, c, work s1, work s2)
      | While (n, c, i, s1) ->
	  While (n, c, i, work s1)
      | DoWhile (n, c, i, s1) ->
	  DoWhile (n, c, i, work s1)
      | Sequence (n, s1, s2) ->
	  Sequence (n, work s1, work s2)
      | Choice (n, s1, s2) ->
	  Choice (n, work s1, work s2)
      | Merge (n, s1, s2) ->
	  Merge (n, work s1, work s2)
      | s -> s
  in
    work stmt

let optimise_in_method prg cls m =
  match m.Method.body with
      None -> m
    | Some body ->
	{ m with Method.body =
	    Some ((optimise_in_statement
		      (List.map (function v -> v.VarDecl.name) m.Method.outpars))
		     body) } 

(* Take a program and try to replace tail calls with a version using
   out special macro. *)
let optimize prg = Program.for_each_method prg optimise_in_method
