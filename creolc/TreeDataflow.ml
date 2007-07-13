(*
 * TreeDataFlow.ml -- Data Flow Analysis for Creol
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

let collect_declarations attribute =
    List.fold_left
	(function map ->
	  function { VarDecl.name = name; VarDecl.var_type = _;
		     VarDecl.init = _ } -> 
            Note.Environment.add name
	      { Note.attribute = attribute;
		Note.label = false;
		(* The value of an attribute is always defined *)
		Note.defined = attribute;
		(* The value of an attribute is always life *)
		Note.life = attribute }
	      map)
	Note.Environment.empty

let collect_declarations attribute =
    List.fold_left
	(function map ->
	  function { var_name = name; var_type = _; var_init = _ } -> 
            Note.Environment.add name
	      { Note.attribute = attribute;
		Note.label = false;
		(* The value of an attribute is always defined *)
		Note.defined = attribute;
		(* The value of an attribute is always life *)
		Note.life = attribute }
	      map)
	Note.Environment.empty

let rec find_definitions l =
  (** Computes the definitions of a variable.

  *)
  List.map definitions_in_declaration l
and definitions_in_declaration =
  function
      Class c -> Class (definitions_in_class c)
    | Interface i -> Interface (definitions_in_interface i)
    | Exception e -> Exception e
    | Datatype d -> Datatype d (* XXX *)
and definitions_in_class c =
  let attrs = collect_declarations true
    (c.Class.parameters @ c.Class.attributes) in
    { c with
      Class.with_defs = List.map (definitions_in_with attrs) c.Class.with_defs }
and definitions_in_interface i =
  i
and definitions_in_with attrs w =
  { w with
    With.methods = List.map (definitions_in_method attrs) w.With.methods }
and definitions_in_method attrs m =
  match m.meth_body with
      None -> m
    | Some body ->
	{ m with meth_body =
	    let note =
	      { Note.file = Note.file (Statement.note body);
		Note.line = Note.line (Statement.note body);
		Note.env = attrs }
	    in
	      Some (definitions_in_statement note body) }
and definitions_in_statement note stm =
  (** Compute the variables defined at a current statement.

      @param attrs is the set of names which are attributes.  They are always
      defined in a program.

      @param note is the updated note of the preceding statement.

      @return The statement with its note updated.  *)
  let define env name label =
    (** Define a name in an environment. *)
    let v =
      { Note.attribute = false;
	Note.label = label;
	Note.defined = true;
	Note.life = false }
    in
      Note.Environment.add name v env
  in
    match stm with
	Skip n ->
	  Skip { n with Note.env = note.Note.env }
      | Assert (n, e) ->
	  Assert ({ n with Note.env = note.Note.env }, e)
      | Assign (n, lhs, rhs) ->
	  Assign ({n with Note.env = note.Note.env }, lhs, rhs)
	(* XXX: Completely broken...
	  Assign ({ n with Note.env = 
	      List.fold_left (fun e n -> define e n false)
		note.Note.env (name lhs)}, lhs, rhs) *)
      | Await (n, g) ->
	  Await ({ n with Note.env = note.Note.env }, g)
      | Release a ->
	  Release { a with Note.env = note.Note.env }
      | AsyncCall (n, None, c, m, a) ->
	  (* XXX: This should not happen, but if we resolve this, we need to
	     rerun this for updating the chain... *)
	  AsyncCall ({ n with Note.env = note.Note.env }, None, c, m, a)
      | AsyncCall (n, Some l, c, m, a) ->
	  AsyncCall ({ n with Note.env = (define note.Note.env l true) },
		    Some l, c, m, a)
      | Reply (n, l, p) ->
	  Reply ({ n with Note.env = note.Note.env } , l, p)
      | Free (n, v) -> assert false
      | SyncCall (n, c, m, ins, outs) ->
	  SyncCall ({ n with Note.env = note.Note.env }, c, m, ins, outs) (* XXX *)
      | AwaitSyncCall (n, c, m, ins, outs) ->
	  AwaitSyncCall ({ n with Note.env = note.Note.env }, c, m, ins, outs) (* XXX *)
      | LocalAsyncCall (n, None, m, ub, lb, i) ->
	  (* XXX: This should not happen, but if we resolve this, we need to
	     rerun this for updating the chain... *)
	  LocalAsyncCall ({ n with Note.env = note.Note.env}, None, m, ub, lb,
			 i)
      | LocalAsyncCall (n, Some l, m, ub, lb, i) ->
	  LocalAsyncCall ({ n with Note.env = (define note.Note.env l true)},
			 Some l, m, ub, lb, i)
      | LocalSyncCall (n, m, u, l, a, r) ->
	  LocalSyncCall ({ n with Note.env = note.Note.env },
			m, u, l, a, r) (* XXX *)
      | AwaitLocalSyncCall (n, m, u, l, a, r) ->
	  AwaitLocalSyncCall ({ n with Note.env = note.Note.env },
		             m, u, l, a, r) (* XXX *)
      | Tailcall (n, m, u, l, a) -> assert false
      | If (n, c, l, r) ->
	  (* Beware, that the new note essentially contains the union
	     of the definitions of both its branches, whereas the first
	     statement of each branch contains the updated note of the
	     preceding statement. *)
	  let nl = (definitions_in_statement note l)
	  and nr = (definitions_in_statement note r) in
	    If ({n with Note.env = Note.join (Statement.note nl).Note.env
		(Statement.note nr).Note.env},
	       c, nl, nr)
      | While (n, c, i, b) ->
	  While ({ n with Note.env = note.Note.env }, c, i,
		definitions_in_statement n b)
      | Sequence (n, s1, s2) ->
	  let ns1 = (definitions_in_statement note s1) in
	  let ns2 = (definitions_in_statement note s2) in
	    Sequence ({n with Note.env = Note.join (Statement.note ns1).Note.env
		(Statement.note ns2).Note.env},
		  ns1, ns2)
	      (* For merge and choice we do not enforce sequencing of the
		 computation of the parts, but we allow the compiler to
		 choose some order *)
      | Merge (n, l, r) -> 
	  let nl = (definitions_in_statement note l)
	  and nr = (definitions_in_statement note r) in
	    Merge ({n with Note.env = Note.join (Statement.note nl).Note.env
		(Statement.note nr).Note.env},
		  nl, nr)
      | Choice (n, l, r) -> 
	  let nl = (definitions_in_statement note l)
	  and nr = (definitions_in_statement note r) in
	    Choice ({n with Note.env = Note.join (Statement.note nl).Note.env
		(Statement.note nr).Note.env},
		   nl, nr)
      | Extern (n, s) -> Extern (n, s)

let rec life_variables tree =
  (** Compute whether a variable is still in use at a position in the
      program.

      The algorithm assumes that the input [tree] has been annotated with
      information about the definitions of variables.  See
      [find_definitions].

      It will perform a back-ward pass and annotate each node with the
      use-information.

      This algorithms has been adapted from the algorithm described in
      Section 9.5 "Next-Use Information" of A.V. Aho, R. Sethi, and J.D.
      Ullman, "Compilers: Principles, Techniques, and Tools",
      Addison-Wesley, 1986.

      Where this algorithm comes from is not clear to me, but it may already
      be mentioned in Knuth, Donald E. (1962), "A History of Writing
      Compilers," Computers and Automation,, December, 1962, reprinted in
      Pollock, Barry W., ed. Compiler Techniques, Auerbach Publishers,
      1972. *)
  List.map uses_in_declaration tree
and uses_in_declaration =
  function
      Class c -> Class (uses_in_class c)
    | Interface i -> Interface (uses_in_interface i)
    | Exception e -> Exception e
    | Datatype d -> Datatype d (* XXX *)
and uses_in_class c =
  { c with Class.with_defs = List.map uses_in_with c.Class.with_defs }
and uses_in_interface i =
  i
and uses_in_with w =
  { w with With.methods = List.map uses_in_method w.With.methods }
and uses_in_method m =
  match m.meth_body with
      None -> m
    | Some body -> { m with meth_body = Some (uses_in_statement body) }
and uses_in_statement =
  function
      Skip _ as s -> s
    | Assert (_, _) as s -> s
    | Assign (a, l, r) -> assert false
    | Await (a, g) -> assert false
    | Release a -> assert false
    | AsyncCall (a, None, c, m, ins) -> assert false
    | AsyncCall (a, Some l, c, m, ins) -> assert false
    | Reply (a, l, outs) -> assert false (* use l and clear p *)
    | Free (a, v) -> assert false
    | SyncCall (a, c, m, ins, outs) -> assert false
    | LocalAsyncCall (a, None, m, lb, ub, ins) -> assert false
    | LocalAsyncCall (a, Some l, m, lb, ub, ins) -> assert false
    | LocalSyncCall (a, m, lb, ub, ins, outs) -> assert false
    | Tailcall (a, m, lb, ub, ins) -> assert false
    | If (a, c, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	let nc = uses_in_expression c in
	  If ({ a with
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
	     nc, ns1, ns2)
    | While (a, c, i, b) -> assert false
    | Sequence (a, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	  Sequence ({ a with
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
		ns1, ns2)
    | Merge (a, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	  Merge ({ a with
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
		ns1, ns2)
    | Choice (a, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	  Choice ({ a with 
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
		 ns1, ns2)
      | Extern (n, s) -> Extern (n, s)
and uses_in_sequence note =
  function
      [] -> assert false
    | [s] -> assert false
    | s::r ->
	let nr = uses_in_sequence note r in
	let ns = uses_in_statement s in
	  ns::nr
and uses_in_expression e = e
