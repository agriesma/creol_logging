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
  help: string;
  dependencies: string list;
  pass: (Note.t, Note.t, Note.t) Declaration.t list ->
			     (Note.t, Note.t, Note.t) Declaration.t list;
  mutable elapsed: float;
  mutable needed: bool;
  mutable dump: bool
}


(** An association list collecting the passes in order. *)
let passes = [
  ( "typecheck" ,
  { help = "Check for type consistency" ;
    dependencies = [];
    pass = CreolTyping.typecheck;
    elapsed = 0.0; needed = true; dump = false } );
  ( "dataflow" ,
  { help = "Compute data flow." ;
    dependencies = [];
    pass = find_definitions;
    elapsed = 0.0; needed = true; dump = false } ) ;
  ( "dead-vars" ,
  { help = "Eliminate dead variables and values." ;
    dependencies = ["dataflow"];
    pass = find_definitions;
    elapsed = 0.0; needed = false; dump = false } ) ;
  ( "tailcall" ,
  { help = "Optimise tail-calls." ;
    dependencies = [];
    pass = optimise_tailcalls;
    elapsed = 0.0; needed = false; dump = false } );
]

let help () =
  let pass_help_line current ps =
    let name = fst ps
    and help = (snd ps).help
    in
      current ^ "    " ^ name ^
	(String.make (11 - String.length name) ' ') ^
	help ^ "\n"
  in
    (List.fold_left pass_help_line "" passes) ^
      "    all        all passes mentioned above."


(** Enable passes.

    Accepts a list of strings, separated by comma or whitespace, and
    enables each pass in this list, as well as its dependencies.

    May raise Arg.Bad if an undefined pass is provided.  *)
let enable arg =
  let rec enable_pass s =
    let slot = try
	List.assoc s passes
      with
	  Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
    in
      slot.needed <- true ;
      List.iter enable_pass slot.dependencies
  in
    if arg <> "all" then
      List.iter enable_pass (Str.split (Str.regexp "[, \t]+") arg)
    else
      (* Enable all *)
      List.iter (fun (_, p) -> p.dump <- true) passes


(** Disable passes.

    Accepts a list of strings, separated by comma or whitespace, and
    enables each pass in this list, as well as its dependencies.

    May raise Arg.Bad if an undefined pass is provided.

    This function will not try to maintain dependencies, so use at your
    own risk.  *)
let disable arg =
  let disable_pass s =
    let slot = try
	List.assoc s passes
      with
	  Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
    in
      slot.needed <- false
  in
    List.iter disable_pass (Str.split (Str.regexp "[, \t]+") arg)


(** Enable dumping after a pass.

    Accepts a list of strings, separated by comma or whitespace, and
    enables dumping after each pass in this list.  If the string is
    "all", then all passes are enabled.

    May raise Arg.Bad if an undefined pass is provided.

    This function will not try to maintain dependencies, so use at your
    own risk.  *)
let dump_after arg =
  let dump_pass s =
    let slot = try
	List.assoc s passes
      with
	  Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
    in
      slot.dump <- true
  in
    if arg <> "all" then
      List.iter dump_pass (Str.split (Str.regexp "[, \t]+") arg)
    else
      (* Enable all *)
      List.iter (fun (_, p) -> p.dump <- true) passes


let execute_dump name pass tree =
  let basename s =
    try
      let n = String.rindex name '.' in
	if "creol" == (String.sub s (n + 1) ((String.length name) - 1)) then
	  (String.sub s 1 (n - 1))
	else
	  s
    with
	Not_found -> s
  in
  let ign a b = () in
    BackendXML.emit ((basename name)  ^ "." ^ pass) Note.to_xml ign ign tree


let execute_passes filename tree =
  let rec execute tree =
    function 
	[] -> tree
      | p::rest -> execute (run p tree) rest
  and run p tree =
    if (snd p).needed then
      begin
	let now = ref (Unix.gettimeofday ()) in
	let _ = Messages.message 1 ("executing " ^ (fst p)) in
      let result =  ((snd p).pass tree) in
      let elapsed =
	(floor (((Unix.gettimeofday ()) -. !now) *. 1000000.0)) /. 1000.0
      in
	(snd p).elapsed <- (snd p).elapsed +. elapsed;
	if (snd p).dump then execute_dump filename (fst p) result ;
	result
end
else
  tree
in
  execute tree passes

(** Write the internal time measurements to standard error.

    The report is written to standard error, because the actual code
    can be written to standard output, and the report is not part of
    this code. *)
let report_timings () =
  let total = ref 0.0 in
  let rec report =
    function
	[] -> prerr_endline ("Total: ...................................... " ^
			     (string_of_float !total) ^ " msec.\n");
      | p::r ->
	  prerr_endline (" " ^ (String.make (38 - String.length (fst p)) '.') ^
			 " " ^ (string_of_float (snd p).elapsed) ^ " msec.");
	  total := !total +. (snd p).elapsed ; report r
  in
    report passes ;
    flush stderr
