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

let inputs : string list ref = ref []

let add_input name = inputs := (!inputs)@[name]


type outputs = {
	mutable maude: string option;
	mutable maude_red_init: bool;
	mutable maude_main: string option;
	mutable xml: string option;
	mutable pretty_print: string option;
}

let outputs = {
	maude = Some "out.maude";
	maude_red_init = false;
	maude_main = None;
	xml = None;
	pretty_print = None;
}

let apply_outputs tree =
  let do_out f =
    function
        None -> ()
      | Some "-" -> f stdout
      | Some s -> f (open_out s)
  and do_xml tree =
    function None -> () | Some s -> CreolIO.creol_to_xml s Note.to_xml tree
  in
  (** Apply the output passes *)
  do_out (function out -> maude_of_creol outputs.maude_red_init outputs.maude_main out tree) outputs.maude ;
  do_out (function out -> pretty_print out tree) outputs.pretty_print;
  do_xml tree outputs.xml

(* Pass management *)

module Passes =
  struct
    type t =
	{ mutable pass_check_types: bool;
	  mutable pass_simplify: bool;
	  mutable pass_lifeness: bool }

    let passes =
      { pass_check_types = false;
	pass_simplify = true;
	pass_lifeness = true }

    let apply tree =
      (** Transform the tree in accordance to the passes enabled by the
	  user. *)
      let current = ref tree in
	if passes.pass_check_types then current := !current else () ;
	if passes.pass_simplify then current := simplify !current else () ;
	if passes.pass_lifeness then current := find_definitions !current
	else ();
	!current
  end

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
    ("-", Arg.Unit (function () -> add_input "-"), "Read from standard input");
    ("-v", Arg.Unit (function () -> ()),
    "  Print some information while processing");
    ("-M", Arg.String ignore,
    "  Compile the files for model checking and write the result to [file]");
    ("-main", Arg.String (function s -> outputs.maude_main <- Some s),
    "  Compile the files for model checking and write the result to [file]");
    ("-red-init", Arg.Unit (function () ->  outputs.maude_red_init <- true),
    "  Generate an output that will reduce init as first step.");
    ("-o", Arg.String (function s ->  outputs.maude <- Some s),
    "  Compile the files for the interpreter and write the result to [file]");
    ("-syntax-only", Arg.Unit (function () ->  outputs.maude <- None),
    "  Do not write any outputs.");
    ("-p", Arg.String (function s -> outputs.pretty_print <- Some s),
    "  Pretty-print the parse tree after processing to [file]");
    ("-x", Arg.String (function s -> outputs.xml <- Some s),
    "  Export the input files to XML file [name]");
    ("-V", Unit show_version, "  Show the version and exit");
    ("--version", Unit show_version, "  Show the version and exit")]
  in
    parse options add_input (Sys.executable_name ^ " [options]") ;
    let tree =
      match !inputs with
	  [] ->  usage options (Sys.executable_name ^ " [options]"); exit 0
	| ["-"] -> CreolIO.from_channel stdin
	| _ ->  CreolIO.from_files !inputs in
      apply_outputs (Passes.apply tree) ;
      exit 0 ;;

main()
