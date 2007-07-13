(*
 * TreeTailcall.ml -- Optimize tailcalls.
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

let tailcall_counter = ref 0

let tailcall_successes () = !tailcall_counter

let optimise_tailcalls prg =
  (** Take a program and try to replace tail calls with a version using
      out special macro. *)
  let rec optimise_declaration =
    function
      Declaration.Class c -> Declaration.Class (optimise_in_class c)
    | Declaration.Interface i -> Declaration.Interface i
    | Declaration.Exception e -> Declaration.Exception e
    | Declaration.Datatype d -> Declaration.Datatype d
  and optimise_in_class c =
    { c with Class.with_defs = List.map optimise_in_with c.Class.with_defs }
  and optimise_in_with w =
    { w with With.methods = List.map optimise_in_method w.With.methods }
  and optimise_in_method m =
    match m.Method.meth_body with
	None -> m
      | Some body ->
	  { m with Method.meth_body =
	      Some ((optimise_in_statement
			(List.map (function v -> v.VarDecl.name) m.Method.meth_outpars))
		       body) } 
  and optimise_in_statement outs s = s
  in
    tailcall_counter := 0;
    List.map optimise_declaration prg
