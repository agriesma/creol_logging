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

open Arg

let inputs : string list ref = ref []

let add_input name = inputs := (!inputs)@[name]


let maude_output = ref (Some "out.maude")

let set_maude_output s =
  maude_output := (match s with ("" | "-") -> None | _ ->  Some s)

let xml_output : string option ref = ref None

let xml_arg s = xml_output := Some s

let handle_xml_note writer note = ()

let apply_outputs tree =
  (** Apply the output passes *)
  (match !maude_output with
      None -> ()
    | Some n -> let out = match n with "-" -> stdout | _ -> open_out n in
		  Creol.maude_of_creol out tree) ;
  (match !xml_output with
      None ->  ()
    | Some s -> CreolIO.creol_to_xml s handle_xml_note tree)

(* Pass management *)

let check_types = ref false
  (** Check the model for type consistency. *)

let pass_simplify = ref true
  (** Simplify the model *)

let apply_passes tree =
  (** Transform the tree in accordance to the passes enabled by the user. *)
  let current = ref tree in
    if !check_types then current := !current else () ;
    if !pass_simplify then current := Creol.simplify !current else () ;
    !current

(** Show the name and the version of the program and exit. *)

let show_version () =
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
		   Version.reldate ^ ")\n" );
  print_string "Copyright (c) 2007 Marcel Kyas\n";
  print_string "This is free software; see the source for copying conditions.\n";
  print_string "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n";
  print_string "PARTICULAR PURPOSE.\n";
  exit 0

let options = [
  ("-", Unit (function () -> add_input "-"), "Read from standard input");
  ("-v", Unit (function () -> ()),
   "  Print some information while processing");
  ("-M", String ignore,
   "  Compile the files for the model checker and write the result to [file]");
  ("-o", String set_maude_output,
   "  Compile the files for the interpreter and write the result to [file]");
  ("-x", String xml_arg,
   "  Export the input files to XML file [name]");
  ("-V", Unit show_version, "  Show the version and exit");
  ("--version", Unit show_version, "  Show the version and exit")
]

let main () =
  parse options add_input (Sys.executable_name ^ " [options]") ;
  let tree =
    match !inputs with
	[] ->  usage options (Sys.executable_name ^ " [options]"); exit 0
      | ["-"] -> CreolIO.from_channel stdin
      | _ ->  CreolIO.from_files !inputs in
    apply_outputs (apply_passes tree) ; exit 0 ;;

main() ;;
