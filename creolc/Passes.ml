(*
 * Passes.ml -- Organize the passes of the compiler.
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

type pass = {
  name: string;
  dependencies: string list;
  pass: (Note.t, Note.t) Declaration.t list ->
			     (Note.t, Note.t) Declaration.t list;
  mutable elapsed: float;
  mutable needed: bool;
  mutable dump: bool
}

let passes = [
  { name = "liveness";
    dependencies = [];
    pass = find_definitions;
    elapsed = 0.0; needed = true; dump = false };
  { name = "deadvars";
    dependencies = ["liveness"];
    pass = find_definitions;
    elapsed = 0.0; needed = false; dump = false };
  { name = "tailcall";
    dependencies = [];
    pass = optimise_tailcalls;
    elapsed = 0.0; needed = false; dump = false };
]

let split str =
  let rec _split str res =
    try
      let p = String.index str ',' in
       _split (String.sub str (p + 1) (String.length str))
	((String.sub str 1 (p - 1))::res)
    with
      Not_found -> res
  in
    _split str []
  

let enable_passes passes =
  ()

let disable_passes passes =
  ()

let dump_passes passes =
  ()

let execute_passes tree =
  let rec execute tree =
    function 
	[] -> tree
      | p::rest -> execute (run p tree) rest
  and run p tree =
    if p.needed then
      begin
	let now = ref (Unix.gettimeofday ()) in
	let result =  (p.pass tree) in
	let elapsed =
	  (floor (((Unix.gettimeofday ()) -. !now) *. 1000000.0)) /. 1000.0
	in
	  p.elapsed <- p.elapsed +. elapsed;
	  if p.dump then ();
	  result
      end
    else
      tree
  in
    execute tree passes

let report_timings () =
  let total = ref 0.0 in
  let rec report =
    function
	[] -> print_string ("Total: ...................................... " ^
			       (string_of_float !total) ^ " msec.\n");
      | p::r ->
	  print_string (" " ^ (String.make (38 - String.length p.name) '.') ^
			   " " ^ (string_of_float p.elapsed) ^ " msec.");
	  total := !total +. p.elapsed ; report r
  in
    report passes
