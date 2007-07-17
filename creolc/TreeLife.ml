(*
 * TreeLife.ml -- Tree-based life variable analysis for Creol programs
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 *)

open Creol
open Expression
open Statement


(** Compute the liveness of variables.

    This is a backwards analysis. *)
let compute tree =
  let rec generate env =
    function
	(This _ | Caller _ | Now _ | Null _ | Nil _ | Bool _ | Int _ |
	    Float _ | String _) -> ()
      | Id (a, v) -> Hashtbl.replace env v ()
      | StaticAttr _ -> ()
      | Tuple (a, l) -> List.iter (generate env) l
      | ListLit (a, l) -> List.iter (generate env) l
      | SetLit (a, l) -> List.iter (generate env) l
      | FieldAccess (a, v, f) -> generate env v
      | Unary (a, o, e) -> generate env e
      | Binary (a, o, l, r) -> List.iter (generate env) [l; r]
      | Expression.If (a, c, t, f) -> List.iter (generate env) [c; t; f]
      | FuncCall (a, f, l) -> List.iter (generate env) l
      | Expression.Label (a, l) -> generate env l
      | New (a, c, l) -> List.iter (generate env) l
      | Expression.Extern _ -> ()
      | SSAId (a, v, n) -> Hashtbl.replace env v ()
      | Phi (a, l) -> List.iter (generate env) l
  in
  let kill env =
    (* This function is used to create a new SSA name, because we
       define a new value for that variable. *)
    function
	LhsVar (n, i) -> Hashtbl.remove env i
      | LhsAttr (n, s, t) -> ()
      | LhsWildcard (n, t) -> ()
      | LhsSSAId (n, i, v) -> Hashtbl.remove env i
  in
  let rec compute_in_statement env =
    function
	Skip n -> ()
      | Assert (n, e) -> generate env e
      | Assign (n, lhs, rhs) ->
	  (** May be vice versa? *)
	  let _ = List.iter (kill env) lhs in
	  let _ = List.iter (generate env) rhs in
	    ()
      | Await (n, g) -> generate env g
      | Posit (n, g) -> generate env g
      | Release n -> ()
      | AsyncCall (n, None, c, m, a) -> List.iter (generate env) (c::a)
      | AsyncCall (n, Some l, c, m, a) ->
	  List.iter (generate env) (c::a) ; kill env l
      | Reply (n, l, p) -> List.iter (kill env) p
      | Free (n, v) -> ()
	  (* List.iter (kill env) v (* FIXME: Ugh! should be rhs *) *)
      | SyncCall (n, c, m, ins, outs) ->
	  let _ = List.iter (generate env) (c::ins) in
	  let _ = List.iter (kill env) outs in
	    ()
      | AwaitSyncCall (n, c, m, ins, outs) ->
	  let _ = List.iter (generate env) (c::ins) in
	  let _ = List.iter (kill env) outs in
	    ()
      | LocalAsyncCall (n, None, m, ub, lb, i) ->
	  let _ = List.iter (generate env) i in
	    ()
      | LocalAsyncCall (n, Some l, m, ub, lb, i) ->
	  let _ = List.iter (generate env) i in
	  let _ = kill env l in
	    ()
      | LocalSyncCall (n, m, u, l, ins, outs) ->
	  let _ = List.iter (generate env) ins in
	  let _ = List.iter (kill env) outs in
	    ()
      | AwaitLocalSyncCall (n, m, u, l, ins, outs) ->
	  let _ = List.iter (generate env) ins in
	  let _ = List.iter (kill env) outs in
	    ()
      | Tailcall (n, m, u, l, ins) ->
	  let _ = List.iter (generate env) ins in
	    ()
      | If (n, c, l, r) ->
	  let _ = compute_in_statement env l in
	  let _ = compute_in_statement env r in
	  let _ = generate env c in
	    ()
      | While (n, c, i, b) ->
	  let _ = compute_in_statement env b in
	  let _ = match i with None -> () | Some inv -> generate env inv in
	  let _ = generate env c in
	    ()
      | Sequence (n, s1, s2) ->
	  let _ = compute_in_statement env s2 in
	  let _ = compute_in_statement env s1 in
	    ()
      | Merge (n, l, r) -> 
	  let _ = compute_in_statement env r in
	  let _ = compute_in_statement env l in
	    ()
      | Choice (n, l, r) -> 
	  let _ = compute_in_statement env r in
	  let _ = compute_in_statement env l in
	    ()
      | Extern (n, s) -> ()
  in
  let compute_in_method m =
    match m.Method.meth_body with
	None -> ()
      | Some b ->
	  (* The final return statement implies that the outparameters are
	     life for the method body. *)
	  let env = Hashtbl.create 32 in
	  let _ = List.iter (function { VarDecl.name = n } ->
	    Hashtbl.replace env n ()) m.Method.meth_outpars
	  in compute_in_statement env b
  in
  let compute_in_with_def w =
    List.iter compute_in_method w.With.methods
  in
  let compute_in_class cls =
    List.iter compute_in_with_def cls.Class.with_defs
  in
  let compute_in_declaration =
    function
	Declaration.Class c -> compute_in_class c
      | Declaration.Interface _ -> ()
      | Declaration.Exception _ -> ()
      | Declaration.Datatype _ -> ()
  in
    List.iter compute_in_declaration tree ; tree
