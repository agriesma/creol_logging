(*
 * TreeUnassert.ml -- Remove all assert statements from a program.
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

(*s Remove all assert statements from a program.
*)

open Creol
open Expression
open Statement

let dependencies = ""

(* Split the assignments.
   
*)
let rec unassert_statement =
  function
    | (Skip _ | Release _ | Prove _ | Assign _ | Await _ | Posit _ |
       AsyncCall _ | Free _ | Bury _ | Get _ | SyncCall _ |
       AwaitSyncCall _ | LocalAsyncCall _ | LocalSyncCall _ |
       AwaitLocalSyncCall _ | MultiCast _ | Discover _ | Tailcall _ |
       StaticTail _ | Return _ | Continue _) as s -> s
    | Assert (a, _) -> Skip a 
    | If (a, c, t, f) ->
	If (a, c, unassert_statement t, unassert_statement f)
    | While (a, c, i, b) ->
	While (a, c, i, unassert_statement b)
    | DoWhile (a, c, i, b) ->
	DoWhile (a, c, i, unassert_statement b)
    | Sequence (a, s1, s2) ->
	Sequence (a, unassert_statement s1, unassert_statement s2)
    | Merge (a, s1, s2) ->
	Merge (a, unassert_statement s1, unassert_statement s2)
    | Choice (a, s1, s2) ->
	Choice (a, unassert_statement s1, unassert_statement s2)
    | Extern _ as s -> s

let unassert_method program cls =
  Method.apply_to_body (fun s -> remove_redundant_skips (unassert_statement s))

let unassert program = Program.for_each_method program unassert_method

