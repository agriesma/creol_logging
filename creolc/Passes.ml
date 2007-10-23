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

(*s A simple pass manager.

The pass manager maintains a list of passes and whether they are
enabled or not.  Individual passes can be enabled and disabled from
the command line.  The pass manager tries to maintain all dependencies
between passes.

*)

open Creol

(*
Defines the type of a pass.  \ocwlowerid{help} represents the help
message for that pass.  \ocwlowerid{dependencies} is a string containing
a comma-separated list of passes this pass depends on.  \ocwlowerid{pass}
is the function representing the program transformation performed by the
pass.  \ocwlowerid{elapsed} is the time needed for executing that pass.
\ocwlowerid{enabled} is a predicate stating whether the pass is enabled.
Finally, \ocwlowerid{dump} is a variable which is true iff the user
requested an XML dump \emph{after} that pass.
*)
 
type pass = {
  help: string;
  dependencies: string;
  pass: Program.t -> Program.t ;
  mutable elapsed: float;
  mutable enabled: bool;
  mutable dump: bool
}

(*
The variable \ocwlowerid{time\_emit} measures the time spent for emitting
the result, i.e., the complete time spent in the backend.
*)
let time_emit = ref 0.0

(*
The variable \ocwlowerid{time\_dump} accumulates the time spend for
emitting state dumps to XML trees.  We think that the time spent here
is not very important, and we cannot reasonably speed it up.
*)

let time_dump = ref 0.0


(*
This association list maintains all passes known to the compiler.
The list \emph{must} be topologically sorted, i.e., if a pass depends
on other passes, then this pass must occur after its dependent passes
in the list.
*)
let passes = [
  ( "typecheck" ,
  { help = "Check for type consistency" ;
    dependencies = "";
    pass = CreolTyping.typecheck;
    elapsed = 0.0; enabled = true; dump = false } );
  ( "lower" ,
  { help = "Expand statements to Core Creol" ;
    dependencies = "";
    pass = TreeLower.pass;
    elapsed = 0.0; enabled = true; dump = false } );
  ( "into-ssa" ,
  { help = "Compute data flow." ;
    dependencies = "lower";
    pass = TreeSSA.into_ssa ;
    elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "life-vars" ,
  { help = "Compute data flow." ;
    dependencies = "lower";
    pass = TreeLife.compute ;
    elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "dead-vars" ,
  { help = "Eliminate dead variables and values." ;
    dependencies = "life-vars" ;
    pass = TreeDeadvar.optimize ;
    elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "tailcall" ,
  { help = "Optimise tail-calls." ;
    dependencies = "lower";
    pass = TreeTailcall.optimize ;
    elapsed = 0.0; enabled = false; dump = false } );
  ( "outof-ssa" ,
  { help = "Convert a tree in SSA back to a non-SSA form." ;
    dependencies = "into-ssa";
    pass = TreeSSA.out_of_ssa ;
    elapsed = 0.0; enabled = false; dump = false } ) ;
]

(*
Compute a help string from the list of passes.
*)
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


(*
Enable passes.

Accepts a list of strings, separated by comma or whitespace, and
enables each pass in this list, as well as its dependencies.

May raise Arg.Bad if an undefined pass is provided.
*)
let rec enable arg =
  let enable_pass s =
    let slot = try
	List.assoc s passes
      with
	  Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
    in
      slot.enabled <- true ; enable slot.dependencies
  in
    if arg <> "all" then
      List.iter enable_pass (Str.split (Str.regexp "[, \t]+") arg)
    else
      (* Enable all *)
      List.iter (fun (_, p) -> p.enabled <- true) passes


(*
Disable passes.

Accepts a list of strings, separated by comma or whitespace, and
enables each pass in this list, as well as its dependencies.

May raise Arg.Bad if an undefined pass is provided.

This function will not try to maintain dependencies, so use at your
own risk.
*)
let disable arg =
  let disable_pass s =
    let slot = try
	List.assoc s passes
      with
	  Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
    in
      slot.enabled <- false
  in
    List.iter disable_pass (Str.split (Str.regexp "[, \t]+") arg)


(*
Enable dumping after a pass.

Accepts a list of strings, separated by comma or whitespace, and
enables dumping after each pass in this list.  If the string is
"all", then all passes are enabled.

Raises Arg.Bad if an undefined pass is provided.
*)
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

(*
The following function is called to execute a dump to XML and to
accumulate the time spent for dumping.  \ocwlowerid{filename} is the
name of the input file.  \ocwlowerid{pass} is the name of the
pass after which the tree is emitted.  \ocwlowerid{tree} is the
abstract syntax tree to emit.
*)
let execute_dump ~filename ~pass ~tree =
  let file =
    (if filename <> "" || filename <> "-" then filename else "creolc.out") ^
      "." ^ pass
  in
  let f () =
    let () = Messages.message 1 ("Writing dump to " ^ file) in
    let () = BackendXML.emit file tree in
    let () = Messages.message 1 ("Finished writing dump to " ^ file) in
      ()
  in
  let ((), elapsed) = Misc.measure f in
    time_dump := !time_dump +. elapsed ;
    ()

(*
The following function accepts an abstract syntax \ocwlowerid{tree},
return by the parser, and applies each enabled pass to that
\ocwlowerid{tree} in order.  If dumping the \ocwlowerid{tree} is
requested after a pass, this function will do so.  Finally, the time
spent for each pass is measured.
*)
let execute_passes filename tree =
  let rec execute tree =
    function 
	[] -> tree
      | p::rest -> execute (run p tree) rest
  and run p tree =
    if (snd p).enabled then
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

(*
This function writes the time measurements to standard error.
The report is written to standard error, because the actual code
can be written to standard output, and the report is not part of
this code.
*)
let report_timings () =
  let total = ref 0.0 in
  let report p =
    if (snd p).enabled then
      prerr_endline ((fst p) ^ ": " ^
			(String.make (38 - String.length (fst p)) '.') ^
			" " ^ (string_of_float (snd p).elapsed) ^ " ms");
    total := !total +. (snd p).elapsed
  in
    prerr_endline ("Parsing: ............................... " ^
		      (string_of_float !Parser.time) ^ " ms");
    List.iter report passes ;
    prerr_endline ("Dumps: ................................. " ^
		      (string_of_float !time_dump) ^ " ms");
    prerr_endline ("Emit: .................................. " ^
		      (string_of_float !time_emit) ^ " ms");
    prerr_endline ("Total: ................................. " ^
		      (string_of_float
			  (!total +. !Parser.time +. !time_dump +. !time_emit)) ^
		      " ms\n")
