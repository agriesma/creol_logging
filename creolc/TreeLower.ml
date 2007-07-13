(*
 * TreeLower.ml -- Transform a tree into core creol.
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

(** A counter used to generate the next fresh label *)
let next_fresh_label = ref 0

let fresh_label () =
  (* make a fresh label *)
  let res = "sync." ^ (string_of_int !next_fresh_label) in
    next_fresh_label := !next_fresh_label + 1 ; res

let pass input =
  (** Normalise an abstract syntax tree by replacing all derived concepts
      with there basic equivalents *)
  let rec lower_expression =
    function
	Unary(a, o, e) ->
	  (* Do not copy the note, since the content should be invariant. *)
	  FuncCall(a, string_of_unaryop o, [lower_expression e])
      | Binary(a, o, l, r) ->
	  (* Do not copy the note, since the content should be invariant. *)
	  FuncCall(a, string_of_binaryop o, [lower_expression l;
					     lower_expression r])
      | FuncCall(a, f, args) -> FuncCall(a, f, List.map lower_expression args)
      | New (a, t, p) -> New (a, t, List.map lower_expression p)
      | t -> t
  and lower_statement =
    function
	Skip _ as s -> s
      | Release _ as s -> s
      | Assert (a, e) -> Assert (a, lower_expression e)
      | Assign (a, s, e) -> Assign (a, s, List.map lower_expression e)
      | Await (a, g) -> Await (a, lower_expression g)
      | AsyncCall (a, None, e, n, p) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards.  It may be better to insert free later, but for this
	     we need smarter semantic analysis. *)
	  Sequence (a, AsyncCall (a,
				 Some ".anon", lower_expression e, n,
				 List.map lower_expression p),
		   Free (a, ".anon"))
      | AsyncCall (a, Some l, e, n, p) ->
	  AsyncCall (a, Some l, lower_expression e, n,
		    List.map lower_expression p)
      | Free _ as s -> s
      | Reply _ as s -> s
      | SyncCall (a, e, n, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
          let ne = lower_expression e
	  and np = List.map lower_expression p
	  and l = fresh_label ()
          in
	    Sequence (a, AsyncCall (a,
				   Some l, ne, n, np),
		     Reply (a, l, r))
      | AwaitSyncCall (a, e, n, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
          let ne = lower_expression e
	  and np = List.map lower_expression p
	  and l = fresh_label ()
          in
	    Sequence (a, AsyncCall (a, Some l, ne, n, np),
		     Sequence(a,
			     Await (a, Label(Expression.note ne, l)),
			     Reply (a, l, r)))
      | LocalAsyncCall (a, None, m, lb, ub, i) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards.  It may be better to insert free later, but for this
	     we need smarter semantic analysis. *)
	  Sequence (a, LocalAsyncCall(a, Some ".anon", m, lb, ub,
				     List.map lower_expression i),
		   Free (a, ".anon"))
      | LocalAsyncCall (a, Some l, m, lb, ub, i) ->
	  LocalAsyncCall (a, Some l, m, lb, ub, List.map lower_expression i)
      | LocalSyncCall (a, m, l, u, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
	  let ni = List.map lower_expression i
	  and lab = fresh_label ()
          in
	    Sequence (a, LocalAsyncCall (a, Some lab, m, l, u, ni),
		     Reply (a, lab, o))
      | AwaitLocalSyncCall (a, m, l, u, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
	  let ni = List.map lower_expression i
	  and lab = fresh_label ()
          in
	    Sequence (a, LocalAsyncCall (a, Some lab, m, l, u, ni),
		     Sequence (a, Await (a,
					 Label(make_expr_note_from_stmt_note a,
					       lab)),
			      Reply (a, lab, o)))
      | Tailcall (a, m, l, u, i) ->
	  Tailcall (a, m, l, u, List.map lower_expression i)
      | If (a, c, t, f) -> If(a, lower_expression c, lower_statement t,
			     lower_statement f)
      | While (a, c, None, b) ->
	  While (a, lower_expression c, None, lower_statement b)
      | While (a, c, Some i, b) ->
	  While (a, lower_expression c, Some (lower_expression i),
		lower_statement b)
      | Sequence (a, s1, s2) ->
	  let ls1 = lower_statement s1
	  and ls2 = lower_statement s2 in
	    Sequence (a, ls1, ls2)
      | Merge (a, s1, s2) -> Merge (a, lower_statement s1,
				   lower_statement s2)
      | Choice (a, s1, s2) -> Choice (a, lower_statement s1,
				     lower_statement s2)
      | Extern _ as s -> s
  and lower_method_variables note vars =
    (** Compute a pair of a new list of local variable declarations
	and a list of assignments used for initialisation.

	if the variable list is empty or no variable in the list has an
	initializer, this function will produce a skip statement as the
	method-call's initialization.  The caller of this function should
	check for this and discard the initalization block.

	The initialisation component of variable declarations will be
	removed. *)
    let lower_method_variable =
      function 
          ({ VarDecl.name = n ; var_type = _ ; init = Some i } as v) ->
	    ([{ v with VarDecl.init = None }],
	    Assign(note, [LhsVar(Expression.note i, n)], [lower_expression i]))
        | v -> ([v], Skip note)
    in
      match vars with
	  [] -> ([], Skip note)
	| [v] -> (lower_method_variable v)
	| v::l ->
	    let vl = lower_method_variable v
	    and ll = lower_method_variables note l in
	      match vl with
		  (vll, Assign _) -> (vll@(fst ll), Sequence(note, (snd vl), (snd ll)))
		| (vll, Skip _) -> (vll@(fst ll), (snd ll))
		| _ -> assert false
  and lower_method m =
    (** Simplify a method definition. *)
    let _ = next_fresh_label := 0 (* Labels must only be unique per method. *)
    in
    match m.Method.meth_body with
	None -> m
      | Some mb  ->
	  let smv = lower_method_variables (Statement.note mb) m.Method.meth_vars in
	    { m with Method.meth_vars = fst smv ;
	      meth_body = Some( if Statement.is_skip_p (snd smv) then
		normalize_sequences (lower_statement mb)
		else
		  Sequence(Statement.note mb, snd smv,
			  normalize_sequences (lower_statement mb))) }
  and lower_with w =
    { w with With.methods = List.map lower_method w.With.methods }
  and lower_inherits =
    function
	(n, e) -> (n, List.map lower_expression e)
  and lower_inherits_list =
    function
	[] -> []
      | i::l -> (lower_inherits i)::(lower_inherits_list l)
  and lower_class c =
    { c with Class.inherits = lower_inherits_list c.Class.inherits;
      Class.with_defs = List.map lower_with c.Class.with_defs }
  and lower_interface i =
    i
  and lower_declaration =
    function
	Declaration.Class c -> Declaration.Class (lower_class c)
      | Declaration.Interface i -> Declaration.Interface (lower_interface i)
      | Declaration.Exception e -> Declaration.Exception e
      | Declaration.Datatype d -> Declaration.Datatype d
  in
    List.map lower_declaration input
