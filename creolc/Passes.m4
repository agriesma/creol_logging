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
open Messages

(* Defines the type of a pass.  \ocwlowerid{help} represents the help
   message for that pass.  \ocwlowerid{dependencies} is a string
   containing a comma-separated list of passes this pass depends on.
   \ocwlowerid{pass} is the function representing the program
   transformation performed by the pass.  \ocwlowerid{elapsed} is the
   time needed for executing that pass.  \ocwlowerid{enabled} is a
   predicate stating whether the pass is enabled.  Finally,
   \ocwlowerid{dump} is a variable which is true iff the user requested
   an XML dump \emph{after} that pass.
*)
  
type pass = {
  help: string;
  dependencies: string;
  pass: Program.t -> Program.t ;
  mutable elapsed: float;
  mutable enabled: bool;
  mutable dump: bool
}

(* The variable \ocwlowerid{time\_parse} measures the time spent for
   lexing and parsing a program.  It accumulates the time spent in the
   front end.
*)
let time_parse = ref 0.0

(* The variable \ocwlowerid{time\_emit} measures the time spent for
   emitting the result, i.e., the complete time spent in the backend.
*)
let time_emit = ref 0.0

(* The variable \ocwlowerid{time\_dump} accumulates the time spend for
   emitting state dumps to XML trees.  We think that the time spent
   here is not very important, and we cannot reasonably speed it up.
*)

let time_dump = ref 0.0


(* This association list maintains all passes known to the compiler.
   The list \emph{must} be topologically sorted, i.e., if a pass
   depends on other passes, then this pass must occur after its
   dependent passes in the list.
*)
let passes = [
  ( "typecheck",
    { help = "Undocumented.";
      dependencies = Typing.dependencies;
      pass = Typing.typecheck;
      elapsed = 0.0; enabled = true; dump = false } );
  ( "unassert",
    { help = "Remove all assertions." ;
      dependencies = TreeUnassert.dependencies ;
      pass = TreeUnassert.unassert ;
      elapsed = 0.0; enabled = false; dump = false } );
  ( "fold",
    { help = "Fold all constants." ;
      dependencies = "typecheck" ;
      pass = TreeFold.optimise ;
      elapsed = 0.0; enabled = false; dump = false } );
  ( "lower" ,
    { help = "Expand statements to Core Creol" ;
      dependencies = TreeFold.dependencies;
      pass = TreeLower.pass;
      elapsed = 0.0; enabled = true; dump = false } );
  ( "devirt" ,
    { help = "Devirtualise attribute access.";
      dependencies = "typecheck";
      pass = TreeDevirt.transform;
      elapsed = 0.0; enabled = false; dump = false } );
  ( "into-ssa" ,
    { help = "Compute data flow." ;
      dependencies = "";
      pass = TreeSSA.into_ssa ;
      elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "split-ass" ,
    { help = "Split multiple assignments into single assignments." ;
      dependencies = TreeSplitAss.dependencies;
      pass = TreeSplitAss.split ;
      elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "def-vars" ,
    { help = "Compute data flow." ;
      dependencies = "";
      pass = TreeDef.analyse ;
      elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "life-vars" ,
    { help = "Compute data flow." ;
      dependencies = "";
      pass = TreeLife.analyse ;
      elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "warn-undef",
    { help = "Check whether uses occur before definitions" ;
      dependencies = CheckUseDef.dependencies ;
      pass = CheckUseDef.analyse ;
      elapsed = 0.0; enabled = true; dump = false } ) ;
  ( "free" ,
    { help = "Insert statements to free labels" ;
      dependencies = TreeFree.dependencies;
      pass = TreeFree.optimize ;
      elapsed = 0.0; enabled = false; dump = false } ) ;
  ( "bury" ,
    { help = "Insert statements to reset dead variables" ;
      dependencies = TreeBury.dependencies ;
      pass = TreeBury.optimize ;
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


(* Compute a help string from the list of passes. *)
let help () =
  let pass_help_line current ps =
    let name = fst ps
    and help = (snd ps).help
    in
      assert (((String.length name) > 0) && ((String.length name) < 11));
      current ^ "    " ^ name ^
	(String.make (11 - String.length name) ' ') ^
	help ^ "\n"
  in
    (List.fold_left pass_help_line "" passes) ^
      "    all        all passes mentioned above."



(* Enable passes.

   Accepts a list of strings, separated by comma or whitespace, and
   enables each pass in this list, as well as its dependencies.

   May raise Arg.Bad if an undefined pass is provided. *)

let rec enable arg =
  if arg <> "all" then
    List.iter enable_pass (Str.split (Str.regexp "[, \t]+") arg)
  else
    (* Enable all *)
    List.iter (fun (_, p) -> p.enabled <- true) passes
and enable_pass s =
  let slot = try
      List.assoc s passes
    with
	Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
  in
    slot.enabled <- true ; enable slot.dependencies

let requires passes =
  let doit p =
    message 1 ("Enabling pass " ^ p ^ ", it is required by the backend") ;
    enable_pass p
  in
    List.iter doit passes





(* Disable a single pass. *)

let disable_pass s =
  let slot = try
      List.assoc s passes
  with
      Not_found -> raise (Arg.Bad ("unknown pass `" ^ s ^ "'"))
  in
    slot.enabled <- false


(* Disable a list of passes. *)

let conflicts passes =
  let doit p =
    message 1 ("Disabling pass " ^ p ^ ", it conflicts with the backend") ;
    disable_pass p
  in
    List.iter doit passes


(* Disable passes.

   Accepts a list of strings, separated by comma or whitespace, and
   enables each pass in this list, as well as its dependencies.

   May raise Arg.Bad if an undefined pass is provided.

   This function will not try to maintain dependencies, so use at your
   own risk.
*)
let disable arg =
    List.iter disable_pass (Str.split (Str.regexp "[, \t]+") arg)


(* Enable dumping after a pass.

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


(*s The following functions comprise the front-end of the compiler.
  The purpose of the front-end is to perform lexical analysis and
  parsing of the input programs.

  Read the contents from a channel and return a abstract syntax tree
  and measure the time used for it.
*)
let parse_from_channel (name: string) (channel: in_channel) =
  let buf = Lexing.from_channel channel in
  let pos = buf.Lexing.lex_curr_p in
  let _ =  buf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = name } in
  let _ = message 1 ("Reading " ^ name) in
  let do_parse () = Parser.main Lexer.token buf in
  let (result, elapsed) = Misc.measure do_parse in
    time_parse := !time_parse +. elapsed ;
    result


(* Read the contents of a file and return an abstract syntax tree.
*)
let parse_from_file (name: string) =
  let exists_p d = Sys.file_exists (d ^ "/" ^ name) in
  let file =
    if ((Sys.file_exists name) || (String.contains name '/')) then
      name
    else
      try
        (List.find exists_p (Config.get_library_path ())) ^ "/" ^ name
      with
          Not_found -> prerr_endline ("cannot find " ^ name) ; exit 1
  in
    parse_from_channel file (open_in file)


(* Read the contents of a list of files and return an abstract syntax
   tree.
*)
let parse_from_files: string list -> Declaration.t list =
  function files ->
    List.fold_left (fun (a: Declaration.t list) (n: string) ->
      (parse_from_file n)@a) [] files


(*s The following functions comprise the \emph{middle end} of the
  compiler.  The middle end will perform semantic analysis and
  transformations on the level of the abstract syntax tree.

  The following function is called to execute a dump to XML and to
  accumulate the time spent for dumping.  \ocwlowerid{filename} is the
  name of the input file.  \ocwlowerid{pass} is the name of the pass
  after which the tree is emitted.  \ocwlowerid{tree} is the abstract
  syntax tree to emit.
*)
let execute_dump ~filename ~pass ~tree =
  let file =
    (if filename <> "" || filename <> "-" then filename else "creolc.out") ^
      "." ^ pass
  in
  let f () =
    let () = message 1 ("Writing dump to " ^ file) in
    ifdef(`BACKEND_XML', `let () = BackendXML.emit file tree in')
    let () = message 1 ("Finished writing dump to " ^ file) in
      ()
  in
  let ((), elapsed) = Misc.measure f in
    time_dump := !time_dump +. elapsed ;
    ()


(* The following function accepts an abstract syntax
   \ocwlowerid{tree}, return by the parser, and applies each enabled
   pass to that \ocwlowerid{tree} in order.  If dumping the
   \ocwlowerid{tree} is requested after a pass, this function will do
   so.  Finally, the time spent for each pass is measured.
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
	  let () = message 1 ("===== Executing " ^ (fst p)) in
          let result = (snd p).pass tree in
	  let () = message 1 ("===== Finished executing " ^ (fst p) ^ "\n\n")
	  in
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


(* This function writes the time measurements to standard error.  The
   report is written to standard error, because the actual code can be
   written to standard output, and the report is not part of this code.
*)
let report_timings () =
  let total = ref 0.0 in
  let report p =
    let t = (snd p).elapsed in
      if (snd p).enabled then
	prerr_endline ((fst p) ^ ": " ^
			 (String.make (38 - String.length (fst p)) '.') ^
			 " " ^ (string_of_float t) ^ " ms");
      total := !total +. t
  in
    prerr_endline ("Parsing: ............................... " ^
		      (string_of_float !time_parse) ^ " ms");
    List.iter report passes ;
    if !time_dump > 0. then
      prerr_endline ("Dumps: ................................. " ^
		       (string_of_float !time_dump) ^ " ms");
    if !time_emit > 0. then
      prerr_endline ("Emit: .................................. " ^
		       (string_of_float !time_emit) ^ " ms");
    prerr_endline ("Total: ................................. " ^
		      (string_of_float
			  (!total +. !time_parse +. !time_dump +. !time_emit)) ^
		      " ms\n")
