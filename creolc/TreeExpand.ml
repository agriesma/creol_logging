(*
 * TreeExpand.ml -- Transform a tree into core Creol.
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

(** Lower a tree by expanding all abbreviations.  The result will be a
    tree which is suitable for the back-ends and other passes of the
    system.
*)

open Creol
open Expression
open Statement

(* Passes which must have been executed before calling any of the functions
   defined in this module. *)

let dependencies = "typecheck"


(** Compute initialisation statements from a list of variable declarations.
    Returns a statement that initialises all the variables according to the
    initialiser in some unspecific order. *)

let initialiser ?(cls="") vdecls =
  let p = function { VarDecl.init = None } -> false | _ -> true in
  let q = function { VarDecl.init = Some (New _) } -> true | _ -> false  in
  let vn, vd = List.partition q (List.filter p vdecls) in
  let f =
    function
      | { VarDecl.name = n } when cls <> "" ->
            LhsAttr(Expression.make_note (), n, Type.Basic cls)
      | { VarDecl.name = n } -> LhsId (Expression.make_note (), n)
  in
  let g =
    function
      | { VarDecl.init = Some e } -> e
      | _ -> assert false
  in
  let h v = Assign (Statement.make_note (), [f v], [g v]) in
  let ns = List.fold_left (fun a v -> Sequence (Statement.make_note (), h v, a)) (Statement.Skip (Statement.make_note ())) vn
  and vs = Assign (Statement.make_note (), List.map f vd, List.map g vd) in
  let s =
    match ns, vs with
      | (_, Assign (_, [], _)) -> ns
      | (Skip _, _) -> vs
      | _ -> Sequence (Statement.make_note (), ns, vs)
  in
    remove_redundant_skips s


let expand_statement program cls meth future_decls fresh_name =
  let rec expand future_decls fresh_name =
    let future_decl l t =
      { VarDecl.name = l; var_type = t; init = None; file = ""; line = 0 }
    in
    let rec make fn =
      let Misc.FreshName (name, fn') = fn () in
	try
	  let _ = Method.find_variable meth name in
	    make fn'
	with
	    Not_found ->
	      begin
		try
		  let _ = Program.find_attr_decl program cls name in
		    make fn'
		with
		    Program.Attribute_not_found _ -> (name, fn')
	      end
    in
      function
	| Skip _ | Release _ | Assert _ | Prove _ | Assign _ | Await _
	| Posit _  as s ->
            (future_decls, fresh_name, s)
	| AsyncCall (a, None, e, n, ((co, dom, Some rng) as s), p) ->
	    (* If a future name is not given, we assign a new one and
	       free it afterwards. *)
	    let (l, fresh_name') = make fresh_name
	    and lt = Type.future rng in
	    let n' = make_expr_note_from_stmt_note a lt in
	      ((future_decl l lt)::future_decls, fresh_name',
	       AsyncCall (a, Some (LhsId (n', l)), e, n, s, p))
	| AsyncCall (a, None, e, n, s, p) ->
            if not (Type.collection_p (Expression.get_type e)) then
	      (* If a future name is not given, we create a new future name.
		 We cannot give a correct type to the future.  If the type
		 checker is run after expanding, it may report errors for
		 this call.  *)
              begin
		let (l, fresh_name') = make fresh_name in
		let lt = Type.future [] in
		let a' = make_expr_note_from_stmt_note a lt in
		  ((future_decl l lt)::future_decls, fresh_name',
		   AsyncCall (a, Some (LhsId (a', l)), e, n, s, p))
	      end
	    else
	      (* The type checker inferred that the callee expression refers
		 to a collection type.  In this case, we convert to a
		 MultiCast statement. *)
	      (future_decls, fresh_name, MultiCast (a, e, n, s, p))
	| AsyncCall _ | Free _ | Bury _ | Get _ as s ->
            (future_decls, fresh_name, s)
	| SyncCall (a, e, n, s, p, r) ->
	    (* Replace the synchronous call by the sequence of an asynchronous
	       call followed by a reply.  This generates a fresh future name.  *)
	    let (l, fresh_name') = make fresh_name
	    and lt = Type.future (List.map get_lhs_type r) in
	    let a' = make_expr_note_from_stmt_note a lt in
	      ((future_decl l lt)::future_decls, fresh_name',
	       Sequence (a, AsyncCall (a, Some (LhsId (a', l)), e, n, s, p),
			 Get (a, Id (a', l), r)))
	| AwaitSyncCall (a, e, n, s, p, r) ->
	    (* Replace the synchronous call by the sequence of an asynchronous
	       call followed by a reply.  This generates a fresh future name.  *)
	    let (l, fresh_name') = make fresh_name
	    and lt = Type.future (List.map get_lhs_type r)
	    in
	    let a' = make_expr_note_from_stmt_note a lt
	    and a'' = make_expr_note_from_stmt_note a Type.bool
	    in
	      ((future_decl l lt)::future_decls, fresh_name',
	       Sequence (a, AsyncCall (a, Some (LhsId (a', l)), e, n, s, p),
			 Sequence(a, Await (a, Label (a'', Id (a', l))),
				  Get (a, Id (a', l), r))))
	| LocalAsyncCall (a, None, m, ((c, dom, Some rng) as s), lb, ub, i) ->
	    (* If a future name is not given, we assign a new one and free it
	       afterwards. *)
	    let (l, fresh_name') = make fresh_name
	    and lt = Type.future rng in
	    let a' = make_expr_note_from_stmt_note a lt in
	      ((future_decl l (Type.future rng))::future_decls, fresh_name',
	       LocalAsyncCall(a, Some (LhsId (a', l)), m, s, lb, ub, i))
	| LocalAsyncCall (a, None, m, s, lb, ub, i) ->
	    (* If a future name is not given, we create a new future name
	       and assign the call to it.  We cannot give a correct type
	       to the future.  If the type checker is run after expanding,
	       we may see a type error since there is no corresponding
	       method declared.  *)
	    let (l, fresh_name') = make fresh_name in
	    let lt = Type.future [] in
	    let a' = make_expr_note_from_stmt_note a lt in
	      ((future_decl l lt)::future_decls, fresh_name',
	       LocalAsyncCall(a, Some (LhsId (a', l)), m, s, lb, ub, i))
	| LocalAsyncCall _ as s ->
	    (future_decls, fresh_name, s)
	| LocalSyncCall (a, m, s, lb, ub, i, o) ->
	    (* Replace the synchronous call by the sequence of an asynchronous
	       call followed by a reply.  This generates a fresh future name.  *)
	    let (l, fresh_name') = make fresh_name
	    and lt = Type.future (List.map get_lhs_type o)
	    in
	    let a' = make_expr_note_from_stmt_note a lt in
	      ((future_decl l lt)::future_decls, fresh_name',
	       Sequence (a, LocalAsyncCall (a, Some (LhsId (a', l)), m, s, lb, ub, i),
			 Get (a, Id (a', l), o)))
	| AwaitLocalSyncCall (a, m, s, lb, ub, i, o) ->
	    (* Replace the synchronous call by the sequence of an asynchronous
	       call followed by a reply.  This generates a fresh future name.  *)
	    let (l, fresh_name') = make fresh_name
	    and lt = Type.future (List.map get_lhs_type o)
	    in
	    let a' = make_expr_note_from_stmt_note a lt 
	    and a'' = make_expr_note_from_stmt_note a Type.bool in
	      ((future_decl l lt)::future_decls, fresh_name',
	       Sequence (a, LocalAsyncCall (a, Some (LhsId (a', l)), m, s, lb, ub, i),
			 Sequence (a, Await (a, Label(a'', Id (a', l))),
				   Get (a, Id (a', l), o))))
	| MultiCast _ | Tailcall _ | StaticTail _ as s ->
            (future_decls, fresh_name, s)
	| If (a, c, t, f) ->
	    let (future_decls', fresh_name', t') =
              expand future_decls fresh_name t
            in
	    let (future_decls'', fresh_name'', f') =
              expand future_decls' fresh_name' f
            in
	      (future_decls'', fresh_name'', If(a, c, t', f'))
	| While (a, c, i, b) ->
	    let (future_decls', fresh_name', b') =
              expand future_decls fresh_name b
            in
	      (future_decls', fresh_name', While (a, c, i, b'))
	| DoWhile (a, c, i, b) ->
	    expand future_decls fresh_name
              (Sequence (a, b, While (a, c, i, b)))
	| Sequence (a, s1, s2) ->
	    let (future_decls', fresh_name', s1') =
              expand future_decls fresh_name s1
            in
	    let (future_decls'', fresh_name'', s2') =
              expand future_decls' fresh_name' s2
            in
	      (future_decls'', fresh_name'', Sequence (a, s1', s2'))
	| Merge (a, s1, s2) ->
	    let (future_decls', fresh_name', s1') =
              expand future_decls fresh_name s1
            in
	    let (future_decls'', fresh_name'', s2') =
              expand future_decls' fresh_name' s2
            in
	      (future_decls'', fresh_name'', Merge (a, s1', s2'))
	| Choice (a, s1, s2) ->
	    let (future_decls', fresh_name', s1') =
              expand future_decls fresh_name s1
            in
	    let (future_decls'', fresh_name'', s2') =
              expand future_decls' fresh_name' s2
            in
	      (future_decls'', fresh_name'', Choice (a, s1', s2'))
	| Return _ | Continue _ | Extern _ as s ->
            (future_decls, fresh_name, s)
  in
    expand future_decls fresh_name



(** Compute a pair of a new list of local variable declarations and a
    list of assignments used for initialisation.

    if the variable list is empty or no variable in the list has an
    initializer, this function will produce a skip statement as the
    method-call's initialization.  The caller of this function should
    check for this and discard the initalization block.

    The initialisation component of variable declarations will be
    removed. *)
let rec expand_method_variables note vars =
  let expand_method_variable = function 
      ({ VarDecl.name = n ; var_type = _ ; init = Some i } as v) ->
	([{ v with VarDecl.init = None }],
	 Assign(note, [LhsId(Expression.note i, n)], [i]))
    | v -> ([v], Skip note)
  in
    match vars with
	[] -> ([], Skip note)
      | [v] -> (expand_method_variable v)
      | v::l ->
	  let vl = expand_method_variable v
	  and ll = expand_method_variables note l in
	    match vl with
		(vll, Assign _) -> (vll@(fst ll), Sequence(note, (snd vl), (snd ll)))
	      | (vll, Skip _) -> (vll@(fst ll), (snd ll))
	      | _ -> assert false



let expand_method program cls meth =
    (** Simplify a method definition. *)
    match meth.Method.body with
      | None -> meth
      | Some mb  ->
	  let (future_decls, _, mb') =
            let fresh_name = Misc.fresh_name_gen "ccglab" in
              expand_statement program cls meth [] fresh_name mb
	  and outs =
	    List.map
	      (fun { VarDecl.name = n } -> (Id (Expression.make_note (), n)))
	      meth.Method.outpars
	  in
	  let mb'' = Sequence (Statement.note mb, mb',
			       Return (Statement.note mb, outs))
	  and (vars', init) =
	    expand_method_variables (Statement.note mb)
	      (future_decls @ meth.Method.vars)
	  in
	    { meth with Method.vars = vars' ;
		body = Some (if Statement.skip_p init then
			       normalize_sequences mb''
			     else
			       normalize_sequences
				 (Sequence (Statement.note mb, init, mb''))) }


(** Lower a Creol program to the "Core Creol" language.
    
    1This function will destroy some statement and expression
    annotations.  Therefore, all semantic analysis performed before
    this function should be repeated after calling this function.

    This should only concern type inference, because all other
    analysis should be performed after this function.

    The following two invariant holds for this function:
    - A type correct program remains type correct and the
    annotations of unchanged statements are the same after
    reconstruction.
    - [expand (expand tree) = expand tree]
*)
let pass input =
  let rec expand_with cls w =
    { w with With.methods = List.map (expand_method input cls) w.With.methods }

  (* Rewrite the class into a expanded form.  This entails expanding of
     all sub-parts of the class, but also moving the direct initialisation
     of attributes into the init method and creating of a suitable init
     method and run method for that class. *)

  and expand_class c =

    (* Make an assignment for all direct assignments of the attribute
       list.  If no assignment is needed, the function returns a skip
       statement. *)

    let a' =
      List.map (fun v -> { v with VarDecl.init = None }) c.Class.attributes
    and assignment = initialiser ~cls:c.Class.name c.Class.attributes
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
	  vars = []; body = Some stmt; location = c.Class.name;
          file = ""; line = 0 }
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
	    invariants = []; file =""; line = 0 } :: w
    in

      (* To expand a class, we add an init and a run method if it is
	 missing, moe all direct attribute initialisations to the init
	 method and expand the list of inherits declarations and method
	 definitions.  Observe that the result of [add_init_and_run] is
	 not yet expanded to normal form. *)

      { c with Class.attributes = a';
	with_defs = List.map (expand_with c) (add_init_and_run with_defs') }
  and expand_interface i =
    i
  and expand_declaration =
    function
	Declaration.Class c -> Declaration.Class (expand_class c)
      | Declaration.Interface i -> Declaration.Interface (expand_interface i)
      | (Declaration.Exception _
      | Declaration.Datatype _
      | Declaration.Function _
      | Declaration.Object _
      | Declaration.Future _) as d -> d
  in
    Program.map input expand_declaration
