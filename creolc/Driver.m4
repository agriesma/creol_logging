(*i
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
i*)

(*s This module contains the main entry point to the compiler.  Here,
  the command line arguments are parsed.  Then it starts the different
  phases of compilation.
*)

open Creol
open Arg

(* A list of all file names to parse. *)
let inputs : string list ref = ref []


(* Add a \ocwlowerid{filename} to the list of input files. *)
let add_input filename = inputs := (!inputs)@[filename]


(* Whether to report the timings after compilation. *)
let times = ref false

module Target =
struct
  type t = Null | Creol | Dot | Maude ifdef(`BACKEND_XML', `| XML')

  let target = ref Maude

  let options = { BackendMaude.target = BackendMaude.Interpreter;
		  red_init = false;
		  main = None }

  let setup () =
    match !target with
	Null -> ()
      | Creol ->
	  Passes.conflicts (BackendCreol.conflicts ()) ;
	  Passes.requires (BackendCreol.requires ())
      | Dot ->
	  Passes.conflicts (BackendDot.conflicts ()) ;
	  Passes.requires (BackendDot.requires ())
      | Maude ->
	  Passes.conflicts (BackendMaude.conflicts options) ;
	  Passes.requires (BackendMaude.requires options)
      ifdef(`BACKEND_XML', `| XML ->
	  Passes.conflicts (BackendXML.conflicts ()) ;
	  Passes.requires (BackendXML.requires ())')

  let targets =
    [ ("none", (fun () -> target := Null), "Do not generate any results.");
      ("creol", (fun () -> target := Creol), "Generate a Creol program");
      ("dot", (fun () -> target := Dot), "Generate diagrams in dot format");
      ("maude", (fun () ->
	options.BackendMaude.target <- BackendMaude.Interpreter ;
	target := Maude),
      "Generate a Maude file suitable for the interpreter");
      ("maudemc",
      (fun () ->
	options.BackendMaude.target <- BackendMaude.Modelchecker ;
	Passes.enable "tailcall" ;
	target := Maude),
      "Generate a Maude file optimized for model checking");
      ("maudert",
      (fun () ->
	options.BackendMaude.target <- BackendMaude.Realtime ;
	target := Maude),
      "Generate a Maude file optimized for real-time simulation");
      ifdef(`BACKEND_XML', ("xml", (fun () -> target := XML), "Generate an XML document")) ]

  let set s =
    let (_, f, _) =
      try
	List.find (fun (x, _, _) -> s = x) targets
      with
	  Not_found -> raise (Arg.Bad ("unknown target " ^ s))
    in
      f ()

  let file = ref "creolc.out"

  let help () =
    let line current (name, _, help) =
      current ^ "\n    " ^ name ^
	(String.make (11 - String.length name) ' ') ^
	help
    in
      List.fold_left line "" targets


  let output tree =
    let do_output out =
      Messages.message 1 "Emitting tree" ;
      match !target with
	  Null -> assert false
	| Creol -> BackendCreol.pretty_print_program out tree
	| Dot -> BackendDot.emit out tree
	| Maude -> BackendMaude.emit options out tree
	ifdef(`BACKEND_XML', `| XML -> BackendXML.emit !file tree', `')
    in
      if !target <> Null then
	match !file with
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
  Set_string Target.file,
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
  ifdef(`BACKEND_XML', `("-d",
  Arg.String Passes.dump_after,
  "  Dump tree after [name] to out.[name].  [name]s are identical to ``-p''");')
  ("-times",
  Arg.Set times,
  "  Print timing information");
  ("-T",
  Arg.String Target.set,
  "[name]   Provides the target of the translation:" ^ (Target.help ()));
  ("-main",
  Arg.String (function s -> Target.options.BackendMaude.main <- Some s),
  "  Declare a main class (must not have class parameters)");
  ("-red-init",
  Arg.Unit (function () -> Target.options.BackendMaude.red_init <- true),
  "  Generate an output that will reduce init as first step");
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
	  Passes.parse_from_channel "*stdin*" stdin
      | _ -> 
	  Passes.parse_from_files !inputs
  in
  let prelude =
    List.map Declaration.hide (Passes.parse_from_file "prelude.creol")
  in
    Target.setup () ;
    Target.output (Passes.execute_passes ifdef(`BACKEND_XML', BackendXML.emit, (fun _ _ -> ())) !Target.file (prelude@tree)) ;
    if !times then Passes.report_timings () ;
    exit 0 ;;


(* Finally, invoke the main function.
*)

main ()
