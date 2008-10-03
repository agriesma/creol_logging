(*
 * TreeWLP.ml -- Tree-based weakest liberal pre-condition computation
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

let dependencies = "typecheck"

let log lvl = Messages.message (lvl + 0)

let logwlp n e =
  if !Messages.verbose >= 0 then
    begin
      Format.set_formatter_out_channel stderr ;
      Format.open_vbox 4 ;
      Format.open_hbox () ;
      Format.print_string (n.file ^ ": " ^ (string_of_int n.line) ^ ":") ;
      Format.close_box () ;
      Format.print_space () ;
      Format.open_box 2 ;
      BackendCreol.print_expression e ;
      Format.close_box () ;
      Format.close_box () ;
      Format.print_newline ()
    end

type env = {
  inv: Expression.t
}

(* Compute life ranges of a method body by traversing it backward. *)

let rec wlp env pred =
  function
    | Skip n ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', Skip n)
    | Assert (n, e) ->
	(* This should give rise to a verification condition
	   e => pred, but this cannot be done in this generator yet.
	   Following Jasmin: *)
	let pred' = Binary (Expression.make_note (), And, pred, e) in
	let () = logwlp n pred' in
          (pred, Assert (n, e))
    | Prove (n, e) ->
	(* This should give rise to a verification condition
	   e => pred, but this cannot be done in this generator yet.
	   Following Jasmin: *)
	let pred' = Binary (Expression.make_note (), And, pred, e) in
	let () = logwlp n pred' in
          (pred', Prove (n, e))
    | Posit (n, e) ->
	(* This should give rise to a verification condition
	   e => pred, but this cannot be done in this generator yet. *)
	let pred' = Binary (Expression.make_note (), And, pred, e) in
	let () = logwlp n pred' in
          (pred', Posit (n, e))
    | Assign (n, lhs, rhs) ->
        let add a l r = Expression.Subst.add (Expression.name l) r a in
	let subst = List.fold_left2 add Expression.Subst.empty lhs rhs in
	let pred' = substitute subst pred in
	let () = logwlp n pred' in
          (pred', Assign (n, lhs, rhs))
    | Await (n, c) ->
	let pred' = pred in
	let () = logwlp n pred' in
	  (* The usual rule is $\{Q\}\mbox{await}\ c\{Q\wedge c\}$, but now
	     we could have any predicate that makes $c$ true. *)
          (pred', Await (n, c))
    | Release n ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', Release n)
    | AsyncCall (n, None, c, m, s, a) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', AsyncCall (n, None, c, m, s, a))
    | AsyncCall (n, Some l, c, m, s, a) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', AsyncCall (n, Some l, c, m, s, a))
    | Get (n, l, p) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', Get (n, l, p))
    | Free (n, v) ->
	assert false
    | Bury (n, v) ->
	assert false
    | SyncCall (n, c, m, s, i, o) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', SyncCall (n, c, m, s, i, o))
    | AwaitSyncCall (n, c, m, s, i, o) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', AwaitSyncCall (n, c, m, s, i, o))
    | LocalAsyncCall (n, None, m, s, ub, lb, i) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', LocalAsyncCall (n, None, m, s, ub, lb, i))
    | LocalAsyncCall (n, Some l, m, s, ub, lb, i) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', LocalAsyncCall (n, Some l, m, s, ub, lb, i))
    | LocalSyncCall (n, m, s, u, l, i, o) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', LocalSyncCall (n, m, s, u, l, i, o))
    | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', AwaitLocalSyncCall (n, m, s, u, l, i, o))
    | MultiCast (n, c, m, s, a) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', MultiCast (n, c, m, s, a))
    | Tailcall (n, c, m, s, ins) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', Tailcall (n, c, m, s, ins))
    | StaticTail (n, m, s, u, l, ins) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', StaticTail (n, m, s, u, l, ins))
    | If (n, c, s1, s2) ->
        let (p1, s1') = wlp env pred s1
	and (p2, s2') = wlp env pred s2 in
	let pred' = Expression.If (Expression.make_note (), c, p1, p2) in
	let () = logwlp n pred' in
	   (pred', If (n, c, s1', s2'))
    | While (n, c, i, b) ->
	(* We have a post-condition $Q$, so we need to generate the
	   verification condition $I\land\neg C \implies Q$ and
	   $I\land C \implies wlp(i, b)$ *)
	let (pred', b') = wlp env i b in
	let () = logwlp n pred' in
          (i, While (n, c, i, b'))
    | DoWhile (n, c, i, b) ->
	let (pred', b') = wlp env i b in
	let () = logwlp n pred' in
          (i, DoWhile (n, c, i, b'))
    | Sequence (n, s1, s2) ->
        let (p2, s2') = wlp env pred s2 in
	let (pred', s1') = wlp env p2 s1 in
	let () = logwlp n pred' in
          (pred', Sequence (n, s1', s2'))
    | Merge _ -> assert false
    | Choice (n, s1, s2) -> 
	let (p1, s1') = wlp env pred s1
	and (p2, s2') = wlp env pred s2 in
	let pred' = Binary (Expression.make_note (), Or, p1, p2) in
	let () = logwlp n pred' in
          (pred', Choice (n, s1', s2'))
    | Continue _ -> assert false
    | Return (n, outs) ->
	let pred' = pred in
	let () = logwlp n pred' in
	  (pred', Return (n, outs))
    | Extern (n, s) ->
	let pred' = pred in
	let () = logwlp n pred' in
          (pred', Extern (n, s))

let compute_in_method program cls meth =
  let env = () in
    match meth.Method.body with
      | None ->
          meth
      | Some b ->
	  let (wlp', b') = wlp env meth.Method.ensures b in
            { meth with Method.body = Some b' }


(* Compute life ranges in a program by mapping the above functions
   through the declarations in the tree. [analyse] is the main
   function to call from outside. *)

let analyse program = Program.for_each_method program compute_in_method
