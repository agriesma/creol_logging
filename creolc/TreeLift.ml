(*
 * TreeLift.ml -- Rewrite a tree into a lifted representation.
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

let dependencies = ""


(* Lift a Creol program from the "Core Creol" language.
   
*)
let pass input =
  let rec lift_expression =
    function
      | Unary (a, o, e) ->
	  Unary (a, o, lift_expression e)
      | Binary (a, o, l, r) ->
	  Binary (a, o, lift_expression l, lift_expression r)
      | FuncCall(a, f, [arg]) when unaryop_p f ->
          Unary (a, unaryop_of_string f, lift_expression arg)
      | FuncCall(a, f, [l; r]) when binaryop_p f ->
          Binary (a, binaryop_of_string f, lift_expression l,
		  lift_expression r)
      | FuncCall(a, f, args) ->
          FuncCall (a, f, List.map lift_expression args)
      | New (a, t, p) ->
	  New (a, t, List.map lift_expression p)
      | Expression.If (a, c, t, f) ->
	  Expression.If (a, lift_expression c, lift_expression t,
			 lift_expression f)
      | t -> t
  and lift_statement =
    function
      | (Skip _ | Release _) as s -> s
      | Assert (a, e) -> Assert (a, lift_expression e)
      | Prove (a, e) -> Prove (a, lift_expression e)
      | Assign (a, s, e) -> Assign (a, s, List.map lift_expression e)
      | Await (a, g) -> Await (a, lift_expression g)
      | Posit (a, g) -> Posit (a, lift_expression g)
      | AsyncCall (a, l, e, n, s, p) ->
	  (* If a label name is not given, we assign a new one and
	     free it afterwards. *)
	  let e' = lift_expression e
	  and p' = List.map lift_expression p in
	     AsyncCall (a, l, e', n, s, p')
      | (Free _ | Bury _ | Get _) as s -> s
      | SyncCall (a, e, n, s, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
          let e' = lift_expression e
	  and p' = List.map lift_expression p
          in
            SyncCall (a, e', n, s, p', r)
      | AwaitSyncCall (a, e, n, s, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
          let e' = lift_expression e
	  and p' = List.map lift_expression p
          in
            AwaitSyncCall (a, e', n, s, p', r)
      | LocalAsyncCall (a, l, m, s, lb, ub, i) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards. *)
	  let i' = List.map lift_expression i in
	     LocalAsyncCall (a, l, m, s, lb, ub, i')
      | LocalSyncCall (a, m, s, lb, ub, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.  *)
	  let i' = List.map lift_expression i in
            LocalSyncCall (a, m, s, lb, ub, i', o)
      | AwaitLocalSyncCall (a, m, s, lb, ub, i, o) ->
	  let i' = List.map lift_expression i in
            AwaitLocalSyncCall (a, m, s, lb, ub, i', o)
      | MultiCast (a, c, m, s, i) ->
	  let c' = lift_expression c
	  and i' = List.map lift_expression i
	  in
            MultiCast (a, c', m, s, i')
      | Discover (a, t, m, s, i) ->
	  let i' = List.map lift_expression i in
            Discover (a, t, m, s, i')
      | Tailcall (a, c, m, s, i) ->
	  let c' = lift_expression c
	  and i' = List.map lift_expression i
	  in
	    Tailcall (a, c', m, s, i')
      | StaticTail (a, m, s, l, u, i) ->
	  let i' = List.map lift_expression i in
	    StaticTail (a, m, s, l, u, i')
      | Return (n, o) ->
	  let o' = List.map lift_expression o in
	    Return (n, o')
      | If (a, c, t, f) ->
	  If (a, lift_expression c, lift_statement t, lift_statement f)
      | While (a, c, i, b) ->
	  While (a, lift_expression c, lift_expression i, lift_statement b)
      | DoWhile (a, c, i, b) ->
          DoWhile (a, lift_expression c, lift_expression i, lift_statement b)
      | Sequence (a, s1, s2) ->
	  Sequence (a, lift_statement s1, lift_statement s2)
      | Merge (a, s1, s2) ->
	  Merge (a, lift_statement s1, lift_statement s2)
      | Choice (a, s1, s2) ->
	  Choice (a, lift_statement s1, lift_statement s2)
      | Continue (a, e) ->
	  Continue (a, lift_expression e)
      | Extern _ as s -> s
  and lift_method_variables vars =

    (* Compute a pair of a new list of local variable declarations and
       a list of assignments used for initialisation.

       if the variable list is empty or no variable in the list has an
       initializer, this function will produce a skip statement as the
       method-call's initialization.  The caller of this function should
       check for this and discard the initalization block.

       The initialisation component of variable declarations will be
       removed. *)

    let lift_method_variable =
      function 
        | { VarDecl.init = Some i } as v ->
	    { v with VarDecl.init = Some (lift_expression i) }
        | v -> v
    in
      List.map lift_method_variable vars
  and lift_method m =
    match m.Method.body with
      | None ->
    { m with Method.vars = (lift_method_variables m.Method.vars) }
      | Some mb  ->
	    { m with Method.vars = (lift_method_variables m.Method.vars) ;
	      body = Some (lift_statement mb) }
  and lift_with w =
    { w with With.methods = List.map lift_method w.With.methods }
  and lift_inherits =
    function
	(n, e) -> (n, List.map lift_expression e)
  and lift_inherits_list =
    function
	[] -> []
      | i::l -> (lift_inherits i)::(lift_inherits_list l)

  (* Rewrite the class into a lifted form.  This entails lifting of
     all sub-parts of the class, but also moving the direct initialisation
     of attributes into the init method and creating of a suitable init
     method and run method for that class. *)

  and lift_class c =

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

      (* To lift a class, we add an init and a run method if it is
	 missing, moe all direct attribute initialisations to the init
	 method and lift the list of inherits declarations and method
	 definitions.  Observe that the result of [add_init_and_run] is
	 not yet lifted to normal form. *)

      { c with Class.inherits = lift_inherits_list c.Class.inherits;
	attributes = a';
	with_defs = List.map lift_with with_defs' }
  and lift_interface i =
    i
  and lift_object o =
    let lift_process p =
      { p with Process.code = lift_statement p.Process.code }
    in
      { o with Object.process = lift_process o.Object.process;
               process_queue = List.map lift_process o.Object.process_queue }
  and lift_declaration =
    function
      | Declaration.Class c -> Declaration.Class (lift_class c)
      | Declaration.Interface i -> Declaration.Interface (lift_interface i)
      | Declaration.Object o -> Declaration.Object (lift_object o)
      | (Declaration.Exception _
      | Declaration.Datatype _
      | Declaration.Function _) as d -> d
  in
    List.map lift_declaration input
