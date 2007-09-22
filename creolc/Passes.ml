(*
 * Passes.ml -- Organize the passes of the compiler.
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

type pass = {
  help: string;
  dependencies: string;
  pass: Declaration.t list -> Declaration.t list ;
  mutable elapsed: float;
  mutable needed: bool;
  mutable dump: bool
}

let id x = x

(* Measure the times of some pseude passes *)
(** Time needed for parsing. *)
let time_parse = ref 0.0

(** Total time spend with writing XML dumps. *)
let time_dump = ref 0.0

(** Time spent in emitting the result. *)
let time_emit = ref 0.0


(** An association list collecting the passes in order. *)
let passes = [
  ( "typecheck" ,
  { help = "Check for type consistency" ;
    dependencies = "";
    pass = CreolTyping.typecheck;
    elapsed = 0.0; needed = true; dump = false } );
  ( "lower" ,
  { help = "Expand statements to Core Creol" ;
    dependencies = "";
    pass = TreeLower.pass;
    elapsed = 0.0; needed = true; dump = false } );
  ( "into-ssa" ,
  { help = "Compute data flow." ;
    dependencies = "lower";
    pass = TreeSSA.into_ssa ;
    elapsed = 0.0; needed = false; dump = false } ) ;
  ( "life-vars" ,
  { help = "Compute data flow." ;
    dependencies = "lower";
    pass = TreeLife.compute ;
    elapsed = 0.0; needed = false; dump = false } ) ;
  ( "dead-vars" ,
  { help = "Eliminate dead variables and values." ;
    dependencies = "life-vars" ;
    pass = id ;
    elapsed = 0.0; needed = false; dump = false } ) ;
  ( "tailcall" ,
  { help = "Optimise tail-calls." ;
    dependencies = "lower";
    pass = TreeTailcall.optimize ;
    elapsed = 0.0; needed = false; dump = false } );
  ( "outof-ssa" ,
  { help = "Convert a tree in SSA back to a non-SSA form." ;
    dependencies = "into-ssa";
    pass = TreeSSA.out_of_ssa ;
    elapsed = 0.0; needed = false; dump = false } ) ;
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
let rec enable arg =
  let enable_pass s =
    let slot = try
	List.assoc s passes
      with
	  Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
    in
      slot.needed <- true ; enable slot.dependencies
  in
    if arg <> "all" then
      List.iter enable_pass (Str.split (Str.regexp "[, \t]+") arg)
    else
      (* Enable all *)
      List.iter (fun (_, p) -> p.needed <- true) passes


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
  let file = (name  ^ "." ^ pass) in
  let f () =
    Messages.message 1 ("Writing dump to " ^ file) ;
    BackendXML.emit file tree ;
    Messages.message 1 ("Finished writing dump to " ^ file)
  in
  let (_, elapsed) = Misc.measure f in
    time_dump := !time_dump +. elapsed ;
    ()

let execute_passes filename tree =
  let rec execute tree =
    function 
	[] -> tree
      | p::rest -> execute (run p tree) rest
  and run p tree =
    if (snd p).needed then
      begin
	let pass () =
	  let _ = Messages.message 1 ("Executing " ^ (fst p)) in
          let result = (snd p).pass tree in
	  let _ = Messages.message 1 ("Finished executing " ^ (fst p)) in
	    result
	in
	let (result, elapsed) = Misc.measure pass
	in
	  (snd p).elapsed <- (snd p).elapsed +. elapsed ;
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
  let report p =
    if (snd p).needed then
      prerr_endline ((fst p) ^ ": " ^
			(String.make (38 - String.length (fst p)) '.') ^
			" " ^ (string_of_float (snd p).elapsed) ^ " ms");
    total := !total +. (snd p).elapsed
  in
    prerr_endline ("Parsing: ............................... " ^
		      (string_of_float !time_parse) ^ " ms");
    List.iter report passes ;
    prerr_endline ("Dumps: ................................. " ^
		      (string_of_float !time_dump) ^ " ms");
    prerr_endline ("Emit: .................................. " ^
		      (string_of_float !time_emit) ^ " ms");
    prerr_endline ("Total: ................................. " ^
		      (string_of_float
			  (!total +. !time_parse +. !time_dump +. !time_emit)) ^
		      " ms\n")
