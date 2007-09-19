(*
 * TreeLower.ml -- Transform a tree into core creol.
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

(** A counter used to generate the next fresh label *)
let next_fresh_label = ref 0

let fresh_label () =
  (* make a fresh label *)
  let res = "label:" ^ (string_of_int !next_fresh_label) in
    next_fresh_label := !next_fresh_label + 1 ; res

let pass input =
  (** Normalise an abstract syntax tree by replacing all derived concepts
      with there basic equivalents *)
  let label_decl l rng =
    match rng with
	Type.Tuple rng' ->
          { VarDecl.name = l; var_type = Type.label rng' ; init = None }
      | _ -> 
          { VarDecl.name = l; var_type = Type.label [rng] ; init = None }
  in
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
  and lower_statement label_decls =
    function
	Skip _ as s -> (label_decls, s)
      | Release _ as s -> (label_decls, s)
      | Assert (a, e) -> (label_decls, Assert (a, lower_expression e))
      | Prove (a, e) -> (label_decls, Prove (a, lower_expression e))
      | Assign (a, s, e) ->
	  (label_decls, Assign (a, s, List.map lower_expression e))
      | Await (a, g) -> (label_decls, Await (a, lower_expression g))
      | Posit (a, g) -> (label_decls, Posit (a, lower_expression g))
      | AsyncCall (a, None, e, n, (co, dom, rng), p) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards.  It may be better to insert free later, but for this
	     we need smarter semantic analysis. *)
	  let l = fresh_label () in
	  ((label_decl l rng)::label_decls,
	   Sequence (a, AsyncCall (a,
				 Some (LhsVar (make_expr_note_from_stmt_note a,
					      l)),
				 lower_expression e, n, (co, dom, rng),
				 List.map lower_expression p),
		   Free (a, [Id (make_expr_note_from_stmt_note a, l)])))
      | AsyncCall (a, Some l, e, n, s, p) ->
	  (label_decls, AsyncCall (a, Some l, lower_expression e, n, s,
		    List.map lower_expression p))
      | Free _ as s -> (label_decls, s)
      | Reply _ as s -> (label_decls, s)
      | SyncCall (a, e, n, (c, dom, rng), p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
          let ne = lower_expression e
	  and np = List.map lower_expression p
	  and l = fresh_label ()
          in
	    ((label_decl l rng)::label_decls, Sequence (a, AsyncCall (a, Some (LhsVar (make_expr_note_from_stmt_note a, l)), ne, n, (c, dom, rng), np),
		     Reply (a, Id (make_expr_note_from_stmt_note a, l), r)))
      | AwaitSyncCall (a, e, n, (c, dom, rng), p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let e' = lower_expression e
	  and p' = List.map lower_expression p
	  and l = fresh_label () in
	  let nn = Expression.note e'
	  in
	    ((label_decl l rng)::label_decls,
	     Sequence (a, AsyncCall (a, Some (LhsVar (make_expr_note_from_stmt_note a, l)), e', n, (c, dom, rng), p'),
		     Sequence(a,
			     Await (a, Label (nn, Id (nn, l))),
			     Reply (a, Id (make_expr_note_from_stmt_note a, l),
				   r))))
      | LocalAsyncCall (a, None, m, (c, dom, rng), lb, ub, i) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards.  It may be better to insert free later, but for this
	     we need smarter semantic analysis. *)
	  let l = fresh_label () in
	  ((label_decl l rng)::label_decls, Sequence (a, LocalAsyncCall(a, Some (LhsVar (make_expr_note_from_stmt_note a, l)), m, (c, dom, rng), lb, ub,
				     List.map lower_expression i),
		   Free (a, [Id (make_expr_note_from_stmt_note a, l)])))
      | LocalAsyncCall (a, Some l, m, s, lb, ub, i) ->
	  (label_decls, LocalAsyncCall (a, Some l, m, s, lb, ub, List.map lower_expression i))
      | LocalSyncCall (a, m, (co, dom, rng), l, u, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let i' = List.map lower_expression i
	  and lab = fresh_label ()
	  in
	    ((label_decl lab rng)::label_decls, Sequence (a, LocalAsyncCall (a, Some (LhsVar (make_expr_note_from_stmt_note a, lab)), m, (co, dom, rng), l, u, i'),
		     Reply (a, Id (make_expr_note_from_stmt_note a, lab), o)))
      | AwaitLocalSyncCall (a, m, (co, dom, rng), l, u, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let ni = List.map lower_expression i
	  and lab = fresh_label ()
	  in
	    ((label_decl lab rng)::label_decls, Sequence (a, LocalAsyncCall (a, Some (LhsVar (make_expr_note_from_stmt_note a, lab)), m, (co, dom, rng), l, u, ni),
		     Sequence (a, Await (a,
					Label(make_expr_note_from_stmt_note a,
					     Id (make_expr_note_from_stmt_note a, lab))),
			      Reply (a, Id (make_expr_note_from_stmt_note a,
					   lab),
				    o))))
      | Tailcall (a, m, (co, dom, rng), l, u, i) ->
	  (label_decls, Tailcall (a, m, (co, dom, rng), l, u, List.map lower_expression i))
      | If (a, c, t, f) ->
	  let (label_decls', t') = lower_statement label_decls t in
	  let (label_decls'', f') = lower_statement label_decls' f in
	    (label_decls'', If(a, lower_expression c, t', f'))
      | While (a, c, None, b) ->
	  let (label_decls', b') = lower_statement label_decls b in
	    (label_decls', While (a, lower_expression c, None, b'))
      | While (a, c, Some i, b) ->
	  let (label_decls', b') = lower_statement label_decls b in
	    (label_decls', While (a, lower_expression c, Some (lower_expression i), b'))
      | Sequence (a, s1, s2) ->
	  let (label_decls', s1') = lower_statement label_decls s1 in
	  let (label_decls'', s2') = lower_statement label_decls' s2 in
	    (label_decls'', Sequence (a, s1', s2'))
      | Merge (a, s1, s2) ->
	  let (label_decls', s1') = lower_statement label_decls s1 in
	  let (label_decls'', s2') = lower_statement label_decls' s2 in
	    (label_decls'', Merge (a, s1', s2'))
      | Choice (a, s1, s2) ->
	  let (label_decls', s1') = lower_statement label_decls s1 in
	  let (label_decls'', s2') = lower_statement label_decls' s2 in
	    (label_decls'', Merge (a, s1', s2'))
      | Extern _ as s -> (label_decls, s)
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
      match m.Method.body with
	  None -> m
	| Some mb  ->
	    let (label_decls, mb') = lower_statement [] mb in
	    let (vars', init) =
	      lower_method_variables (Statement.note mb')
		(label_decls @ m.Method.vars)
	    in
	      { m with Method.vars = vars' ;
		body = Some (if Statement.is_skip_p init then
		    normalize_sequences mb'
		  else
		    Sequence(Statement.note mb, init, normalize_sequences mb')) }
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
    (* Make an init method *)
    let lhs n =
      Expression.LhsAttr (Expression.dummy_note, n, Type.Basic c.Class.name)
    in
    let rec build =
      function
	  [] -> ([], [], [])
	| ({ VarDecl.name = n; init = Some i } as v)::l ->
	    let (v', n', i') = build l in
              ({ v with VarDecl.init = None }::v', (lhs n)::n', i::i')
	| v::l ->
	    let (v', n', i') = build l in (v::v', n', i')
    in
    let (a', d', n') = build c.Class.attributes in
    let with_defs' =
      match (d', n') with
	  ([], []) -> c.Class.with_defs
	| _ ->
	    let assign = Assign(Statement.dummy_note, d', n') in
	    let upd_init =
	      function
		  { Method.name = "init"; inpars = []; outpars = [];
		    body = None } as m ->
		    { m with Method.body = Some assign }
		| { Method.name = "init"; inpars = []; outpars = [];
		    body = Some s } as m ->
		    { m with Method.body =
			Some (Sequence(Statement.dummy_note, assign, s)) }
		| m -> m
	    in
	      List.map
		(function
		    { With.co_interface = Type.Internal; methods = m } as w ->
		      { w with With.methods = List.map upd_init m }
		  | w -> w)
		c.Class.with_defs
    in
    let add_init_and_run w =
      let empty_method name =
	{ Method.name = name; coiface = Type.Internal;
	  inpars = []; outpars = []; vars = [];
	  body = Some (Skip Statement.dummy_note) }
      in
      (* We use the invariant that each class declaration has at most one
	 with-block with the internal co-interface and that it is always
	 the first in the list. *)
        if (0 < (List.length w)) &&
	   ((List.hd w).With.co_interface = Type.Internal)
	then
	  (* We have an internal with block.  It should be the first, 
	     so we try to locate it and add the two methods. *)
	  let mk name =
	    let p =
	      function
	        { Method.name = n; coiface = Type.Internal; inpars = [];
		  outpars = [] } when n = name -> true
	        | _ -> false
	    in
	      if List.exists p (List.hd w).With.methods then
		[]
	      else
		let _ = Messages.warn Messages.MissingMethod "**" 0
		  ("Class " ^ c.Class.name ^ " does not provide " ^ name)
		in
		  [ empty_method name ]
	  in
	    let m' =
	      (mk "init") @ (mk "run") @ ((List.hd w).With.methods)
	    in
	      { (List.hd w) with With.methods = m' }::(List.tl w)
        else
	  (* Since we do not have an internal with block we can both an init
	     and a run method to the class. *)
	  { With.co_interface = Type.Internal;
	    methods = [ empty_method "init" ; empty_method "run" ];
	    invariants = [] } :: w
    in
      { c with Class.inherits = lower_inherits_list c.Class.inherits;
	with_defs = List.map lower_with (add_init_and_run with_defs') }
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
