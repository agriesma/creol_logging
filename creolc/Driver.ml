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
  type t = Null | Creol | Dot | Maude | XML

  let target = ref Maude

  let file = ref "creolc.out"

  let options = { BackendMaude.target = BackendMaude.Interpreter;
		  red_init = false;
		  main = None }

  let set =
    function
	"none" -> target := Null
      | "creol" -> target := Creol
      | "dot" -> target := Dot
      | "maude" ->
	  options.BackendMaude.target <- BackendMaude.Interpreter ;
	  target := Maude
      | "maudemc" ->
	  options.BackendMaude.target <- BackendMaude.Modelchecker ;
	  Passes.enable "tailcall" ;
	  target := Maude
      | "maudert" ->
	  options.BackendMaude.target <- BackendMaude.Realtime ;
	  target := Maude
      | "xml" -> target := XML
      | s -> raise (Arg.Bad ("unknown target " ^ s))

  let output tree =
    let do_output out =
      Messages.message 1 "Emitting tree" ;
      match !target with
	  Null -> assert false
	| Creol -> BackendCreol.emit out tree
	| Dot -> BackendDot.emit out tree
	| Maude -> BackendMaude.emit options out tree
	| XML -> BackendXML.emit !file tree
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
  "Copyright (c) 2007 Marcel Kyas\n" ^
  "This is free software; see the source for copying conditions.\n" ^
  "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n" ^
  "PARTICULAR PURPOSE.\n"


(* Show the name and the version of this program as well as its
   license information and exit. *)
let show_version () =
  (** Show the name and the version of the program and exit. *)
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
		   Version.reldate ^ ")\n" );
  print_string license ;
  exit 0


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
  "[name]   Enable warning:\n" ^
    "    all        Enable all warnings");
  ("-W",
  Arg.String Messages.disable,
  " [name]   Disable the warning.  [name]s are the same as for `-w'");
  ("-p",
  Arg.String Passes.enable,
  "{name ,}  Enable passes:\n" ^ (Passes.help ()));
  ("-P",
  Arg.String Passes.disable,
  "  Disable the pass [name].  [name]s are the same as for `-t'");
  ("-d",
  Arg.String Passes.dump_after,
  "  Dump tree after [name] to out.[name].  [name]s are identical to `-p'");
  ("-times",
  Arg.Unit (function () -> times := true),
  "  Print timing information");
  ("-target",
  Arg.String Target.set,
  "[name]   Provides the target of the translation:\n" ^
    "    none       Do not generate any result\n" ^
    "    creol      Write out a creol program\n" ^
    "    maude      Write a maude file suitable for the interpreter\n" ^
    "    maudemc    Write a maude file suitable for the model checker\n" ^
    "    xml        Write the final tree as an XML file.");
  ("-main",
  Arg.String (function s -> Target.options.BackendMaude.main <- Some s),
  "  Compile the files for model checking and write the result to [file]");
  ("-red-init",
  Arg.Unit (function () ->  Target.options.BackendMaude.red_init <- true),
  "  Generate an output that will reduce init as first step.");
  ("-V", Unit show_version, "  Show the version and exit");
  ("-version", Unit show_version, "  Show the version and exit");
  ("--version", Unit show_version, "  Show the version and exit")]


(* The main function parses the command line arguments, parses all
   input programs and executes all phases of the compilation.
*)
let main () =
  parse options add_input (Sys.executable_name ^ " [options]") ;
  let tree =
    match !inputs with
	[] ->  usage options (Sys.executable_name ^ " [options]"); exit 0
      | [""] | ["-"] -> CreolParser.parse_from_channel "*stdin*" stdin
      | _ ->  CreolParser.parse_from_files !inputs
  in
  let prelude =
    List.map Declaration.hide (CreolParser.parse_from_file "prelude.creol")
  in
    Target.output (Passes.execute_passes !Target.file (prelude@tree)) ;
    if !times then Passes.report_timings () ;
    exit 0 ;;


(* Finally, invoke the main function.
*)

main ()
