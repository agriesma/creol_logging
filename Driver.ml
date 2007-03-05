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

let files : string list ref = ref []

(** Show the name and the version of the program and exit. *)

let show_version () =
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
		   Version.reldate ^ ")\n" );
  print_string "Copyright (c) 2007 Marcel Kyas\n";
  print_string "This is free software; see the source for copying conditions.\n";
  print_string "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n";
  print_string "PARTICULAR PURPOSE.\n";
  exit 0;;

let from_file name = files := (!files)@[name]

let options = [
  ("-v", Unit (function () -> ()),
   "  Print some information while processing");
  ("-V", Unit show_version,
   "  Show the version and exit");
  ("--version", Unit show_version, "  Show the version and exit")]
;;

let usage = Sys.executable_name ^ " [options]" ;;



let main () =
  parse options from_file usage ;
  Creol.maude_of_creol stdout (Creol.simplify (CreolIO.from_files (!files)));
  exit 0;;

main() ;;
