(*
 * Driver.ml -- The main routine.
 *
 * This file is part of creolcomp
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

(** Main program.

    @author Marcel Kyas
    @version 0.0
    @since   0.0
 *)

open Creol
open Arg

let verbose = ref false

let inputs : string list ref = ref []

let times = ref false

let add_input name = inputs := (!inputs)@[name]

module Target =
  struct
    type t = No | Creol | Maude | MaudeMC | XML

    let target = ref Maude

    let file = ref "creolc.out"

    let options = { Maude.modelchecker = false; red_init = false; main = None }

    let set =
	function
	    "none" -> target := No
	  | "creol" -> target := Creol
	  | "maude" -> options.Maude.modelchecker <- false; target := Maude
	  | "maudemc" -> options.Maude.modelchecker <- true; target := MaudeMC
	  | "xml" -> target := XML
	  | s -> raise (Arg.Bad ("unknown target " ^ s))

    let output tree =
      let out =
	match !file with
          | "-" -> stdout
          | s -> open_out s
      in
	match !target with
	    No -> ()
	  | Creol -> pretty_print out tree
	  | Maude | MaudeMC ->
	      let id x = x in
		Maude.of_creol options out (lower tree id id id)
	  | XML -> CreolIO.creol_to_xml !file Note.to_xml (fun a b -> ()) (fun a b -> ()) tree
  end

(* Pass management *)

let show_version () =
  (** Show the name and the version of the program and exit. *)
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
		   Version.reldate ^ ")\n" );
  print_string "Copyright (c) 2007 Marcel Kyas\n";
  print_string "This is free software; see the source for copying conditions.\n";
  print_string "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n";
  print_string "PARTICULAR PURPOSE.\n";
  exit 0

let main () =
  let options = [
    ("-",
     Arg.Unit (function () -> add_input "-"), "Read from standard input");
    ("-o",
     Set_string Target.file,
     "  Write the output to file");
    ("-v",
     Arg.Unit (function () -> verbose := true),
     "  Print some information while processing");
    ("-w",
     Arg.Set_string (ref ""),
     "[name]   Enable warning:\n" ^
     "    all        Enable all warnings");
    ("-W",
     Arg.Set_string (ref ""),
     " [name]   Disable the warning.  [name]s are the same as for `-w'");
    ("-d",
     Arg.Set_string (ref ""),
     "  Dump tree after [name] to out.[name].  [name]s are identical to `-p'");
    ("-p",
     Arg.Set_string (ref ""),
     "[name]   Enable the pass:\n" ^
     "    all        All passes described below\n" ^
     "    lifeness   Determine if variables are life or not\n" ^
     "    deadvars   Eliminate dead variables\n" ^
     "    tailcall   Optimize tail calls");
    ("-P",
     Arg.Set_string (ref ""),
     "  Disable the pass [name].  [name]s are the same as for `-t'");
    ("-times",
     Arg.Unit (function () -> times := true),
     "  Print timing information");
    ("-target",
     Arg.String Target.set,
     "[name]   Provides the target of the translation:\n" ^
     "    none       Do not generate any result\n" ^
     "    creol      Write out a creol program\n" ^
     "    maude      Write a maude file suitable for the interpreter\n" ^
     "    maudemc    Write a maude file suitable for the model checker");
    ("-main",
     Arg.String (function s -> Target.options.Maude.main <- Some s),
     "  Compile the files for model checking and write the result to [file]");
    ("-red-init",
     Arg.Unit (function () ->  Target.options.Maude.red_init <- true),
     "  Generate an output that will reduce init as first step.");
    ("-V", Unit show_version, "  Show the version and exit");
    ("-version", Unit show_version, "  Show the version and exit");
    ("--version", Unit show_version, "  Show the version and exit")]
  in
    parse options add_input (Sys.executable_name ^ " [options]") ;
    let tree =
      match !inputs with
	  [] ->  usage options (Sys.executable_name ^ " [options]"); exit 0
	| ["-"] -> CreolIO.from_channel stdin
	| _ ->  CreolIO.from_files !inputs in
      Target.output (Passes.execute_passes tree) ;
      if !times then Passes.report_timings();
      exit 0 ;;

main()
