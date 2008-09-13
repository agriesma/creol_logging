(*
 * TreeSplitAss.ml -- Split multiple assignments to single assignments.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2008 by Marcel Kyas
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

(*s Split all multiple assignment statements to single assignment statements.
*)

open Creol
open Expression
open Statement

let dependencies = "into-ssa"

(* Split the assignments.
   
*)
let rec split_in_statement =
  function
    | (Skip _ | Release _ | Assert _ | Prove _ as s) -> s
    | Assign (a, s, e) ->
	let s' = List.map2 (fun v' e' -> Assign (a, [v'], [e'])) s e in
	  List.fold_left (fun res ass -> Sequence (a, res, ass))
	    (List.hd s') (List.tl s')
    | (Await _ | Posit _ | AsyncCall _ | Free _ | Bury _ | Reply _ |
       SyncCall _ | AwaitSyncCall _ | LocalAsyncCall _ | LocalSyncCall _ |
       AwaitLocalSyncCall _ | MultiCast _ | Discover _ | Tailcall _ |
       StaticTail _ | Return _ ) as s -> s
    | If (a, c, t, f) -> If(a, c, split_in_statement t, split_in_statement f)
    | While (a, c, i, b) -> While (a, c, i, split_in_statement b)
    | DoWhile (a, c, i, b) -> DoWhile (a, c, i, split_in_statement b)
    | Sequence (a, s1, s2) ->
	Sequence (a, split_in_statement s1, split_in_statement s2)
    | Merge (a, s1, s2) ->
	Merge (a, split_in_statement s1, split_in_statement s2)
    | Choice (a, s1, s2) ->
	Choice (a, split_in_statement s1, split_in_statement s2)
    | (Continue _ | Extern _) as s -> s

let split_in_method program cls = Method.apply_to_body split_in_statement

let split program = Program.for_each_method program split_in_method

