(*
 * TreeDevirt.ml -- Devirtualize attribute access and method calls.
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


(* Log messages for definedness analysis *)
let log l = Messages.message (l + 0)

let devirt_statement program cls meth stmt =
  let rec devirt_expression =
    function
	(This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ |
	     Bool _ | Int _ | Float _ | String _ | History _ ) as e -> e
      | Id (n, v) -> 
	  if Method.local_p meth v then
	    Id (n, v)
	  else
	    let cls' = Program.find_class_of_attr program cls v in
	      StaticAttr (n, v, Type.Basic cls'.Class.name)
      | StaticAttr (n, v, Type.Basic c) ->
	    let cls' = Program.find_class_of_attr program
	      (Program.find_class program c) v
	    in
	      StaticAttr (n, v, Type.Basic cls'.Class.name)
      | StaticAttr (n, v, _) -> assert false
      | Tuple (n, l) -> Tuple (n, List.map devirt_expression l)
      | ListLit (n, l) -> ListLit (n, List.map devirt_expression l)
      | SetLit (n, l) -> SetLit (n, List.map devirt_expression l)
      | MapLit (n, l) ->
	  let f (d, r) = (devirt_expression d, devirt_expression r) in
	    MapLit (n, List.map f l)
      | Expression.If (n, c, t, f) ->
	  Expression.If (n, devirt_expression c, devirt_expression t,
			 devirt_expression f)
      | FuncCall (n, f, l) ->
	  FuncCall (n, f, List.map devirt_expression l)
      | Expression.Label (n, l) ->
	  Expression.Label (n, devirt_expression l)
      | New (n, c, l) -> New (n, c, List.map devirt_expression l)
      | Choose (n, v, t, e) ->
	  Choose (n, v, t, devirt_expression e)
      | Exists (n, v, t, e) ->
	  Exists (n, v, t, devirt_expression e)
      | Forall (n, v, t, e) ->
	  Forall (n, v, t, devirt_expression e)
      | ObjLit _ as e -> e
      | LabelLit (n, l) -> LabelLit (n, List.map devirt_expression l)
      | Expression.Extern _ as e -> e
      | SSAId (_, v, _) as e -> assert (Method.local_p meth v); e
      | Phi (n, l) -> Phi (n, List.map devirt_expression l)
  in
  let devirt_lhs =
    function
      | LhsId (n, v) ->
	  if Method.local_p meth v then
	     LhsId (n, v)
	  else
	    let cls' = Program.find_class_of_attr program cls v in
	      LhsAttr (n, v, Type.Basic cls'.Class.name)
      | LhsAttr (n, v, Type.Basic c) ->
	    let cls' = Program.find_class_of_attr program
	      (Program.find_class program c) v
	    in
	      LhsAttr (n, v, Type.Basic cls'.Class.name)
      | LhsAttr (n, v, _) -> assert false
      | LhsWildcard _ as l -> l
      | LhsSSAId (_, i, _) as l -> assert (Method.local_p meth i); l
  in
  let rec work =
    function
      | Assert (n, e) -> Assert (n, devirt_expression e)
      | Prove (n, e) -> Prove (n, devirt_expression e)
      | Assign (n, lhs, rhs) ->
	  Assign (n, List.map devirt_lhs lhs, List.map devirt_expression rhs)
      | Await (n, c) -> Await (n, devirt_expression c)
      | Posit (n, c) -> Posit (n, devirt_expression c)
      | AsyncCall (n, None, c, m, s, i) ->
	  AsyncCall (n, None, c, m, s, List.map devirt_expression i)
      | AsyncCall (n, Some l, c, m, s, i) ->
	  AsyncCall (n, Some (devirt_lhs l), c, m, s,
		     List.map devirt_expression i)
      | Get (n, l, p) ->
	  Get (n, devirt_expression l, List.map devirt_lhs p)
      | Free (n, v) -> Free (n, List.map devirt_lhs v)
      | Bury (n, v) -> Bury (n, List.map devirt_lhs v)
      | SyncCall (n, c, m, s, i, o) ->
	  SyncCall (n, devirt_expression c, m, s,
		    List.map devirt_expression i, List.map devirt_lhs o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  AwaitSyncCall (n, devirt_expression c, m, s,
			 List.map devirt_expression i,
			 List.map devirt_lhs o)
      | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	  LocalAsyncCall (n, None, m, s, ub, lb,
			  List.map devirt_expression i)
      | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	  LocalAsyncCall (n, Some (devirt_lhs l), m, s, ub, lb, 
			  List.map devirt_expression i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  LocalSyncCall (n, m, s, u, l, List.map devirt_expression i,
			 List.map devirt_lhs o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  AwaitLocalSyncCall (n, m, s, u, l, List.map devirt_expression i,
			      List.map devirt_lhs o)
      | MultiCast (n, c, m, s, i) ->
	  MultiCast (n, devirt_expression c, m, s,
		     List.map devirt_expression i)
      | Tailcall (n, c, m, s, i) ->
	  Tailcall (n, devirt_expression c, m, s, List.map devirt_expression i)
      | StaticTail (n, m, s, ub, lb, i) ->
	  StaticTail (n, m, s, ub, lb, List.map devirt_expression i)
      | If (n, c, l, r) ->
	  If (n, devirt_expression c, work l, work r)
      | While (n, c, i, b) ->
	  While (n, devirt_expression c, devirt_expression i, work b)
      | DoWhile (n, c, i, b) ->
	  DoWhile (n, devirt_expression c, devirt_expression i, work b)
      | Sequence (n, s1, s2) ->
	  Sequence (n, work s1, work s2)
      | Merge (n, s1, s2) -> Merge (n, work s1, work s2)
      | Choice (n, s1, s2) -> Choice (n, work s1, work s2)
      | s -> s
  in
    work stmt

(* Compute defined ranges of a method body by traversing it forward. *)

let devirt_method program cls meth =
  let () = log 2
    ("Devirtualising in " ^ cls.Class.name ^ "::" ^ meth.Method.name)
  in
    { meth with Method.body = 
	match meth.Method.body with
	    None -> None
	  | Some b -> Some (devirt_statement program cls meth b) }


(* Compute defined ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let transform program = Program.for_each_method program devirt_method
