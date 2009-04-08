(*
 * UpdateCompiler.ml -- Drive the compilation of updates.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2009 by Marcel Kyas
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

(* The license under which this software is distributed. *)
let license =
  "Copyright (c) 2007, 2008, 2009 Marcel Kyas\n" ^
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


(** {4 Run-time configuration.} *)

(** Whether to report the timings after compilation. *)
let times = ref false

(** Show the configuration after parsing *)
let show_config_flag = ref false

let input_env = ref ""

let output_env = ref "gamma"

let state_file = ref ""

let output_file = ref "creolupdc.out"

let subtarget = ref BackendMaude.Interpreter

let inputs = ref []

let add_input f = inputs := f::(!inputs)


let show_config_p () = !show_config_flag

let show_config () =
  print_endline ("Environment") ;
  print_endline ("CREOL_LIBRARY_PATH = " ^ (String.concat ":" (Config.get_library_path ())))

(** A list of all command line options accepted by this program. This
    list is used by ocamls functions for parsing arguments given to the
    command line. *)
let options = [
  ("-ie",
   Set_string input_env,
   "file  Read the previous environment from file");
  ("-oe",
   Set_string output_env,
   "file  Write the new environment to file");
  ("-state",
   Set_string state_file,
   "file  Name of a file to read the Maude configuration from");
  ("-o",
   Set_string output_file,
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
  ("-show-config",
   Arg.Set show_config_flag,
   "  Show the configuration.");
  ("-V", Unit show_version, "  Show the version and exit");
  ("-version", Unit show_version, "  Show the version and exit");
  ("--version", Unit show_version, "  Show the version and exit")]


let load_input_env () =
  let prelude =
    Program.hide_all (Passes.parse_from_file CreolParser.main "prelude.creol")
  in
    if !input_env <> "" then
      let tree = Passes.parse_from_file CreolParser.main !input_env in
	Passes.execute_passes BackendXML.emit !input_env
          (Program.concat [prelude; tree])
    else
      begin
	prerr_endline ("please provide an input environment file") ;
	exit 1
      end

let load_state () =
  if !state_file <> "" then
    CMCParser.parse_from_file !state_file
  else
    begin
      prerr_endline ("please provide a Maude state file") ;
      exit 1
    end


(* The main function parses the command line arguments, parses all
   input programs and executes all phases of the compilation.
*)
let main () =
  parse options add_input (Sys.executable_name ^ " [options]") ;
  if show_config_p () then show_config () ;
  let program = load_input_env () in
  let update =
    let tree =
      match !inputs with
        | [] ->
            print_endline "No input files given.  Use `-help' for help." ;
            exit 0
        | [""] | ["-"] ->
            Passes.parse_from_channel UpdateParser.main "*stdin*" stdin
        | _ ->
            Passes.parse_from_files UpdateParser.main !inputs
    in
      Passes.execute_passes BackendXML.emit !output_env
        (Program.concat [program; tree])
  in
  let update' = UpdateDepend.depend program update
  and state = load_state () in
  let program' = Program.apply_updates program update' in
  let program'' =
    let f program cls =
      function
        | { Method.body = None } as mtd ->
            mtd
        | { Method.body = Some b } as mtd ->
            { mtd with Method.body =
                Some (Statement.remove_runtime_statements b) }
    in
      Program.for_each_method program' f
  in
  let () = BackendMaude.emit (BackendMaude.features_of_subtarget "updates") stdout (Program.concat [update'; state])
  and () =
    let out_channel = open_out (!output_env ^".creol") in
      BackendCreol.pretty_print_program out_channel program''
  in
    if !times then Passes.report_timings () ;
    exit 0
    ;;


(* Finally, invoke the main function to start the program. *)
main ()
