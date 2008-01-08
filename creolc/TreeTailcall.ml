(*
 * TreeTailcall.ml -- Optimize tailcalls.
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

(*s

*)

open Creol
open Expression
open Statement

let tailcall_counter = ref 0

let tailcall_successes () = !tailcall_counter

let optimise_in_statement stmt = stmt

let optimise_in_method prg cls m =
  match m.Method.body with
      None -> m
    | Some body ->
	{ m with Method.body =
	    Some ((optimise_in_statement
		      (List.map (function v -> v.VarDecl.name) m.Method.outpars))
		     body) } 

(* Take a program and try to replace tail calls with a version using
   out special macro. *)
let optimize prg = Program.for_each_method prg optimise_in_method
