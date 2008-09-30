(*
 * CheckUseDef.ml -- Check that each use has been defined before.
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

open Creol
open Expression
open Statement

let dependencies = "def-vars"

(* Log messages for lifeness analysis *)
let log l = Messages.message (l + 0)

let compute_in_body ~program ~cls ~meth =
  let rec uses =
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
	     Bool _ | Int _ | Float _ | String _ | History _) -> IdSet.empty
      | Id (_, v)  ->
	  if Method.local_p meth v then IdSet.singleton v else IdSet.empty
      | StaticAttr _ ->
	  IdSet.empty
      | Tuple (_, el) | ListLit (_, el) | SetLit (_, el)
      | FuncCall (_, _, el) | New (_, _, el) | LabelLit (_, el)
      | Phi (_, el) ->
	  List.fold_left add IdSet.empty el
      | Unary (_, _, e) | Expression.Label (_, e)
      | Choose (_, _, _, e) | Exists (_, _, _, e) | Forall (_, _, _, e) ->
	  uses e
      | Binary (_, _, l, r) ->
	  IdSet.union (uses l) (uses r)
      | Expression.If (_, c, t, f) ->
	  List.fold_left add IdSet.empty [c; t; f]
      | ObjLit _ | Expression.Extern _ ->
	  IdSet.empty
      | SSAId (_, v, n) ->
	  assert (Method.local_p meth v); IdSet.singleton v
  and add a e =
    IdSet.union (uses e) a
  in
  let rec compute_in_statement =
    let warn n undef =
       let vars = String.concat ", " (IdSet.elements undef) in
	 Messages.warn Messages.Undefined n.file
	   n.line (vars ^ " may be used before defined")
    in
    function
      | Skip _ | Release _ | Bury _ -> ()
      | Assert (n, e) | Prove (n, e) | Await (n, e) | Posit (n, e)
      | Get (n, e, _) | Continue (n, e) ->
	  let undef = IdSet.diff (uses e) n.must_def in
	    if (IdSet.is_empty undef) then
	      ()
	    else
	      warn n undef
      | Assign (n, _, el)
      | LocalAsyncCall (n, _, _, _, _, _, el)
      | LocalSyncCall (n, _, _, _, _, el, _)
      | AwaitLocalSyncCall (n, _, _, _, _, el, _)
      | Discover (n, _, _, _, el)
      | StaticTail (n, _, _, _, _, el)
      | Return (n, el) ->
	  let uses' = List.fold_left add IdSet.empty el in
	  let undef = IdSet.diff uses' n.must_def in
	    if (IdSet.is_empty undef) then
	      ()
	    else
	      warn n undef
      | AsyncCall (n, _, c, _, _, el)
      | SyncCall (n, c, _, _, el, _) 
      | AwaitSyncCall (n, c, _, _, el, _)
      | MultiCast (n, c, _, _, el)
      | Tailcall (n, c, _, _, el) ->
	  let uses' = List.fold_left add IdSet.empty (c::el) in
	  let undef = IdSet.diff uses' n.must_def in
	    if (IdSet.is_empty undef) then
	      ()
	    else
	      warn n undef
      | If (n, e, l, r) ->
	  let undef = IdSet.diff (uses e) n.must_def in
	    if (IdSet.is_empty undef) then
	      begin
	        compute_in_statement l;
	        compute_in_statement r
	      end
	    else
	      warn n undef
      | While (n, c, i, b) | DoWhile (n, c, i, b) ->
	  let uses' = List.fold_left add IdSet.empty [c; i] in
	  let undef = IdSet.diff uses' n.must_def in
	    if (IdSet.is_empty undef) then
	      compute_in_statement b
	    else
	      warn n undef
      | Sequence (_, s1, s2) | Choice (_, s1, s2) -> 
	  compute_in_statement s1;
	  compute_in_statement s2
      | Merge _ -> assert false
      | Extern _ -> ()
  in
    match meth.Method.body with
      | None -> ()
      | Some b -> compute_in_statement b


let compute_in_method program cls meth =
  let () = Messages.message 2
    ("Compute life ranges in " ^ cls.Class.name ^ "::" ^ meth.Method.name)
  in
    match meth.Method.body with
	None -> meth
      | Some b -> let () = compute_in_body program cls meth in meth


(* Compute life ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let analyse program = Program.for_each_method program compute_in_method
