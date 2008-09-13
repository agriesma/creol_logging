(*
 * TreeLower.ml -- Transform a tree into core Creol.
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

(*s Lower a tree by expanding all abbreviations.  The result will be a
  tree which is suitable for the back-ends and other passes of the
  system.
*)

open Creol
open Expression
open Statement

(* Passes which must have been executed before calling any of the functions
   defined in this module. *)

let dependencies = "typecheck"


(* A counter used to generate the next fresh label *)
let next_fresh_label = ref 0


(* Mke a fresh label *)
let fresh_label () =
  let res = "label:" ^ (string_of_int !next_fresh_label) in
  let () = incr next_fresh_label in
    res

(* Create a note for an expression from the information provided by a
   statement and type information.

   Called during splitting of statements. *)
let make_expr_note_from_stmt_note ~stmt t =
        { Expression.file = stmt.Statement.file;
          line = stmt.Statement.line;
          ty = t }

(* Lower a Creol program to the "Core Creol" language.
   
   This function will destroy some statement and expression
   annotations.  Therefore, all semantic analysis performed before
   this function should be repeated after calling this function.

   This should only concern type inference, because all other
   analysis should be performed after this function.

   The following two invariant holds for this function:
   \begin{itemize}
   \item A type correct program remains type correct and the
     annotations of unchanged statements are the same after
     reconstruction.
   \item [lower (lower tree) == lower tree]
   \end{itemize}
*)
let pass input =
  let label_decl l t =
    { VarDecl.name = l; var_type = t; init = None }
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
      | Expression.If (a, c, t, f) ->
          Expression.If (a, lower_expression c, lower_expression t,
                         lower_expression f)
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
      | AsyncCall (a, None, e, n, ((co, dom, Some rng) as s), p) ->
	  (* If a label name is not given, we assign a new one and
	     free it afterwards. *)
	  let e' = lower_expression e
	  and p' = List.map lower_expression p
	  and l = fresh_label ()
	  and lt = Type.label rng in
	  let n' = make_expr_note_from_stmt_note a lt in
	    ((label_decl l lt)::label_decls,
	     AsyncCall (a, Some (LhsId (n', l)), e', n, s, p'))
      | AsyncCall (a, None, e, n, s, p) ->
	  let e' = lower_expression e
	  and p' = List.map lower_expression p
	  in
            if not (Type.collection_p (Expression.get_type e')) then
	      (* If a label name is not given, we create a new label name.
                 We cannot give a correct type to the label.  If the type
                 checker is run after lowering, it may report errors for
                 this call.  *)
              begin
	        let l = fresh_label () in
	        let lt = Type.label [] in
	        let a' = make_expr_note_from_stmt_note a lt in
	          ((label_decl l lt)::label_decls,
	           AsyncCall (a, Some (LhsId (a', l)), e', n, s, p'))
	      end
	    else
	      (* The type checker inferred that the callee expression refers
		 to a collection type.  In this case, we convert to a
	         MultiCast statement. *)
	      (label_decls, MultiCast (a, e', n, s, p'))
      | AsyncCall (a, Some l, e, n, s, p) ->
	  let e' = lower_expression e
	  and p' = List.map lower_expression p in
	    (label_decls, AsyncCall (a, Some l, e', n, s, p'))
      | Free _ as s -> (label_decls, s)
      | Bury _ as s -> (label_decls, s)
      | Reply _ as s -> (label_decls, s)
      | SyncCall (a, e, n, s, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
          let e' = lower_expression e
	  and p' = List.map lower_expression p
	  and l = fresh_label ()
	  and lt = Type.label (List.map get_lhs_type r) in
	  let a' = make_expr_note_from_stmt_note a lt in
	    ((label_decl l lt)::label_decls,
	    Sequence (a, AsyncCall (a, Some (LhsId (a', l)), e', n, s, p'),
		     Reply (a, Id (a', l), r)))
      | AwaitSyncCall (a, e, n, s, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let e' = lower_expression e
	  and p' = List.map lower_expression p
	  and l = fresh_label ()
	  and lt = Type.label (List.map get_lhs_type r)
	  in
	  let a' = make_expr_note_from_stmt_note a lt
	  and a'' = make_expr_note_from_stmt_note a Type.bool
	  in
	    ((label_decl l lt)::label_decls,
	    Sequence (a, AsyncCall (a, Some (LhsId (a', l)), e', n, s, p'),
		     Sequence(a, Await (a, Label (a'', Id (a', l))),
			     Reply (a, Id (a', l), r))))
      | LocalAsyncCall (a, None, m, ((c, dom, Some rng) as s), lb, ub, i) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards. *)
	  let i' = List.map lower_expression i
	  and l = fresh_label ()
	  and lt = Type.label rng in
	  let a' = make_expr_note_from_stmt_note a lt in
	    ((label_decl l (Type.label rng))::label_decls,
	     LocalAsyncCall(a, Some (LhsId (a', l)), m, s, lb, ub, i'))
      | LocalAsyncCall (a, None, m, s, lb, ub, i) ->
	  (* If a label name is not given, we create a new label name
	     and assign the call to it.  We cannot give a correct type
	     to the label.  If the type checker is run after lowering,
	     we may see a type error since there is no corresponding
	     method declared.  *)
	  let i' = List.map lower_expression i
	  and l = fresh_label () in
	  let lt = Type.label [] in
	  let a' = make_expr_note_from_stmt_note a lt in
	    ((label_decl l lt)::label_decls,
	     LocalAsyncCall(a, Some (LhsId (a', l)), m, s, lb, ub, i'))
      | LocalAsyncCall (a, Some l, m, s, lb, ub, i) ->
	  let i' = List.map lower_expression i in
	    (label_decls, LocalAsyncCall (a, Some l, m, s, lb, ub, i'))
      | LocalSyncCall (a, m, s, lb, ub, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let i' = List.map lower_expression i
	  and l = fresh_label ()
	  and lt = Type.label (List.map get_lhs_type o)
	  in
	  let a' = make_expr_note_from_stmt_note a lt in
	    ((label_decl l lt)::label_decls,
	    Sequence (a, LocalAsyncCall (a, Some (LhsId (a', l)), m, s, lb, ub, i'),
		     Reply (a, Id (a', l), o)))
      | AwaitLocalSyncCall (a, m, s, lb, ub, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let i' = List.map lower_expression i
	  and l = fresh_label ()
	  and lt = Type.label (List.map get_lhs_type o)
	  in
	  let a' = make_expr_note_from_stmt_note a lt 
	  and a'' = make_expr_note_from_stmt_note a Type.bool in
	    ((label_decl l lt)::label_decls,
	    Sequence (a, LocalAsyncCall (a, Some (LhsId (a', l)), m, s, lb, ub, i'),
		     Sequence (a, Await (a, Label(a'', Id (a', l))),
			      Reply (a, Id (a', l), o))))
      | MultiCast (a, t, m, s, i) ->
	  (* If a label name is not given, we create a new label name.
             We cannot give a correct type to the label.  If the type
             checker is run after lowering, it may report errors for
             this call.  *)
	  let i' = List.map lower_expression i in
            (label_decls, MultiCast (a, t, m, s, i'))
      | Tailcall (a, c, m, s, i) ->
	  let c' = lower_expression c
	  and i' = List.map lower_expression i
	  in
	    (label_decls, Tailcall (a, c', m, s, i'))
      | StaticTail (a, m, s, l, u, i) ->
	  let i' = List.map lower_expression i in
	    (label_decls, StaticTail (a, m, s, l, u, i'))
      | If (a, c, t, f) ->
	  let (label_decls', t') = lower_statement label_decls t in
	  let (label_decls'', f') = lower_statement label_decls' f in
	    (label_decls'', If(a, lower_expression c, t', f'))
      | While (a, c, i, b) ->
	  let (label_decls', b') = lower_statement label_decls b in
	    (label_decls', While (a, lower_expression c, lower_expression i, b'))
      | DoWhile (a, c, i, b) ->
	  lower_statement label_decls (Sequence (a, b, While (a, c, i, b)))
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
	    (label_decls'', Choice (a, s1', s2'))
      | Continue (a, e) -> (label_decls, Continue (a, lower_expression e))
      | Extern _ as s -> (label_decls, s)
  and lower_method_variables note vars =

    (* Compute a pair of a new list of local variable declarations and
       a list of assignments used for initialisation.

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
	    Assign(note, [LhsId(Expression.note i, n)], [lower_expression i]))
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
	    let (label_decls, mb') = lower_statement [] mb 
	    and outs =
	      List.map
		(fun { VarDecl.name = n } -> (Id (Expression.make_note (), n)))
		m.Method.outpars
	    in
	    let mb'' = Sequence (Statement.note mb, mb',
				 Return (Statement.note mb, outs))
	    and (vars', init) =
	      lower_method_variables (Statement.note mb)
		(label_decls @ m.Method.vars)
	    in
	      { m with Method.vars = vars' ;
		body = Some (if Statement.skip_p init then
		    normalize_sequences mb''
		  else
		    normalize_sequences
		      (Sequence (Statement.note mb, init, mb''))) }
  and lower_with w =
    { w with With.methods = List.map lower_method w.With.methods }
  and lower_inherits =
    function
	(n, e) -> (n, List.map lower_expression e)
  and lower_inherits_list =
    function
	[] -> []
      | i::l -> (lower_inherits i)::(lower_inherits_list l)

  (* Rewrite the class into a lowered form.  This entails lowering of
     all sub-parts of the class, but also moving the direct initialisation
     of attributes into the init method and creating of a suitable init
     method and run method for that class. *)

  and lower_class c =

    (* Make an assignment for all direct assignments of the attribute
       list.  If no assignment is needed, the function returns a skip
       statement. *)

    let (a', assignment) =
      let rec build =
	function
	    [] -> ([], [], [])
	  | ({ VarDecl.name = n; init = Some i } as v)::l ->
	      let lhs n = Expression.LhsAttr (Expression.make_note (), n,
					     Type.Basic c.Class.name)
	      and (v', n', i') = build l
	      in
		({ v with VarDecl.init = None }::v', (lhs n)::n', i::i')
	  | v::l ->
	      let (v', n', i') = build l in (v::v', n', i')
      in
	match build c.Class.attributes with
	    (a', [], []) ->
	      (a', Skip (Statement.make_note ()))
	  | (a', d', n') when List.length d' = List.length n' ->
	      (a', Assign (Statement.make_note (), d', n'))
	  | _ ->
	      assert false
    in
    let with_defs' =
      if Statement.skip_p assignment then
	c.Class.with_defs
      else
	begin
	  let upd_init =
	    function
		{ Method.name = "init"; inpars = []; outpars = [];
		  body = None } as m ->
		  { m with Method.body = Some assignment }
	      | { Method.name = "init"; inpars = []; outpars = [];
		  body = Some s } as m ->
		  { m with Method.body =
		      Some (Sequence(Statement.make_note (), assignment, s)) }
	      | m -> m
	  in
	    List.map
	      (function
		  { With.co_interface = Type.Internal; methods = m } as w ->
		    { w with With.methods = List.map upd_init m }
		| w -> w)
	      c.Class.with_defs
	end
    in

    (* Add the init an run method to the body if it does not exist
       yet. *)

    let add_init_and_run w =

      (* Make a method which is called [name] and which has [stmt] as
	 its body. *)

      let make_method name stmt =
	{ Method.name = name; coiface = Type.Internal;
	  inpars = []; outpars = [];
	  requires = Expression.Bool (Expression.make_note (), true);
	  ensures = Expression.Bool (Expression.make_note (), true);
	  vars = []; body = Some stmt; location = c.Class.name }
      in

	(* We use the invariant that each class declaration has at
	   most one with-block with the internal co-interface and that
	   it is always the first in the list. *)

        if (0 < (List.length w)) &&
	  ((List.hd w).With.co_interface = Type.Internal)
	then

	  (* We have an internal with block.  It should be the first,
	     so we try to locate it and add the two methods. *)

	  let mk name stmt =
	    let p =
	      function
	          { Method.name = n; coiface = Type.Internal; inpars = [];
		    outpars = [] } when n = name -> true
	        | _ -> false
	    in
	      if List.exists p (List.hd w).With.methods then
		[]
	      else

		(* Print a warning if either init or run are missing. *)

		let () =
		  let w =
		    match name with
		        "init" -> Messages.MissingInit
		      | "run" -> Messages.MissingRun
		      | _ -> assert false
		  in
		    Messages.warn w c.Class.file c.Class.line
		      ("Class " ^ c.Class.name ^ " does not provide a " ^ name ^
			  " method" )
		in
		  [ make_method name stmt ]
	  in

	  (* Update the list of methods by adding or changing the
	     method if found. *)

	  let m' =
	    List.concat [(mk "init" assignment);
			 (mk "run" (Skip (Statement.make_note ())));
			 ((List.hd w).With.methods)]
	  in
	    { (List.hd w) with With.methods = m' }::(List.tl w)
        else

	  (* We do not have a with declaration with the internal
	     co-interface.  In this case we just create a new with block
	     with the two missing methods and prepend it to the class. *)

	  { With.co_interface = Type.Internal;
	    methods = [ make_method "init" assignment ;
			make_method "run" (Skip (Statement.make_note ()))];
	    invariants = [] } :: w
    in

      (* To lower a class, we add an init and a run method if it is
	 missing, moe all direct attribute initialisations to the init
	 method and lower the list of inherits declarations and method
	 definitions.  Observe that the result of [add_init_and_run] is
	 not yet lowered to normal form. *)

      { c with Class.inherits = lower_inherits_list c.Class.inherits;
	attributes = a';
	with_defs = List.map lower_with (add_init_and_run with_defs') }
  and lower_interface i =
    i
  and lower_declaration =
    function
	Declaration.Class c -> Declaration.Class (lower_class c)
      | Declaration.Interface i -> Declaration.Interface (lower_interface i)
      | (Declaration.Exception _
      | Declaration.Datatype _
      | Declaration.Function _
      | Declaration.Object _) as d -> d
  in
    List.map lower_declaration input
