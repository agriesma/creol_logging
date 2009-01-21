(*
 * Driver.ml -- The main routine.
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

(** This module contains the main entry point to the compiler.  Here,
  the command line arguments are parsed.  Then it starts the different
  phases of compilation.
*)

open Creol
open Arg


(** A list of all file names to parse. *)
let inputs : string list ref = ref []

(** Add a [filename] to the list of input files. *)
let add_input filename = inputs := (!inputs)@[filename]

(** Whether to report the timings after compilation. *)
let times = ref false

(** The name of the output file. *)
let output = ref "creolc.out"

(** The name of the target. *)
let target = ref "maude"

(** The name of the subtarget. *)
let subtarget = ref "interpreter"

module Target =
struct

  let setup () =
    match !target with
	"none" -> ()
      | "creol" ->
	  Passes.conflicts (BackendCreol.conflicts ()) ;
	  Passes.requires (BackendCreol.requires ())
      | "dot" ->
	  Passes.conflicts (BackendDot.conflicts ()) ;
	  Passes.requires (BackendDot.requires ())
      | "maude" ->
          let options = BackendMaude.features_of_subtarget !subtarget in
	  let _ = Passes.conflicts (BackendMaude.conflicts options) in
	  let _ = Passes.requires (BackendMaude.requires options) in
	    ()
      | "xml" ->
	  Passes.conflicts (BackendXML.conflicts ()) ;
	  Passes.requires (BackendXML.requires ())
      | _ ->
          prerr_endline ("Unknown target " ^ !target) ;
	  exit 1

  let targets =
    [ ("none",	"Do not generate any results.");
      ("creol", "Generate a Creol program");
      ("dot",	"Generate diagrams in dot format");
      ("maude",	"Generate a Maude file suitable for the interpreter");
      ("xml",	"Generate an XML file that represents the abstract syntax tree.");
    ]


  let help () = Misc.help targets


  let output tree =
    let do_output out =
      Messages.message 1 "Emitting tree" ;
      match !target with
	  "none" -> assert false
	| "creol" -> BackendCreol.pretty_print_program out tree
	| "dot" -> BackendDot.emit out tree
	| "maude" ->
            let options = BackendMaude.features_of_subtarget !subtarget in
              BackendMaude.emit options out tree
	| "xml" -> BackendXML.emit !output tree
    in
      if !target <> "none" then
	match !output with
	    "" -> assert false
          | "-" ->
	      let (_, elapsed) = Misc.measure (fun () -> do_output stdout) in
		Passes.time_emit := !Passes.time_emit +. elapsed
          | s ->
	      let out = open_out s in
	      let (_, elapsed) = Misc.measure (fun () -> do_output out)
	      in
		close_out out ;
		Passes.time_emit := !Passes.time_emit +. elapsed

end


(* The license under which this software is distributed. *)
let license =
  "Copyright (c) 2007, 2008 Marcel Kyas\n" ^
  "This is free software; see the source for copying conditions.\n" ^
  "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n" ^
  "PARTICULAR PURPOSE.\n"


(* Show the name and the version of this program as well as its
   license information and exit. *)
let show_version () =
  (** Show the name and the version of the program and exit. *)
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
		   Version.release ^ " of " ^ Version.reldate ^ ")\n" );
  print_string license ;
  exit 0

let show_config_flag = ref false

let show_config_p () = !show_config_flag

let show_config () =
  print_endline ("Environment") ;
  print_endline ("CREOL_LIBRARY_PATH = " ^ (String.concat ":" (Config.get_library_path ())))


(* A list of all command line options accepted by this program. This
   list is used by ocamls functions for parsing arguments given to the
   command line.
*)
let options = [
  ("-",
  Arg.Unit (function () -> add_input "-"), "Read from standard input");
  ("-o",
  Set_string output,
  "  Write the output to file");
  ("-v",
  Arg.Unit (function () -> incr Messages.verbose),
  "  Print some information while processing");
  ("-w",
  Arg.String Messages.enable,
  "{name,}  Enable warning:\n" ^ (Messages.help_warnings ()));
  ("-W",
  Arg.String Messages.disable,
  "{name,}  Disable the warning.  Names are the same as for `-w'");
  ("-p",
  Arg.String Passes.enable,
  "{name,}  Enable passes:\n" ^ (Passes.help ()));
  ("-P",
  Arg.String Passes.disable,
  "  Disable the pass [name].  [name]s are the same as for `-p'");
  ("-d",
  Arg.String Passes.dump_after,
  "  Dump tree after [name] to out.[name].  [name]s are identical to ``-p''");
  ("-times",
  Arg.Set times,
  "  Print timing information");
  ("-T",
  Arg.Set_string target,
  "[name]   Provides the target of the translation:\n" ^ (Target.help ()));
  ("-m",
  Arg.Set_string subtarget,
  "[name]   Provides a subtarget, if the target supports it");
  ("-show-config",
   Arg.Set show_config_flag,
   "  Show the configuration.");
  ("-V", Unit show_version, "  Show the version and exit");
  ("-version", Unit show_version, "  Show the version and exit");
  ("--version", Unit show_version, "  Show the version and exit")]


(* The main function parses the command line arguments, parses all
   input programs and executes all phases of the compilation.
*)
let main () =
  parse options add_input (Sys.executable_name ^ " [options]") ;
  if show_config_p () then show_config () ;
  let tree =
    match !inputs with
	[] ->
	  print_endline "No input files given.  Use `-help' for help." ;
	  exit 0
      | [""] | ["-"] ->
	  Passes.parse_from_channel CreolParser.main "*stdin*" stdin
      | _ -> 
	  Passes.parse_from_files CreolParser.main !inputs
  in
  let prelude = Program.hide_all (Passes.parse_from_file CreolParser.main "prelude.creol") in
    Target.setup () ;
    Target.output ((Passes.execute_passes BackendXML.emit) !output (Program.concat [ prelude; tree ])) ;
    if !times then Passes.report_timings () ;
    exit 0 ;;


(* Finally, invoke the main function.
*)

main ()
