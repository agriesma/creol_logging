(*
 * CMCValid.ml -- Parse the output of the Maude interpreter and print it.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2008 by Marcel Kyas
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


open CMCParser

(* The license under which this software is distributed. *)
let license =
  "Copyright (c) 2007, 2008 Marcel Kyas\n" ^
  "This is free software; see the source for copying conditions.\n" ^
  "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n" ^
  "PARTICULAR PURPOSE.\n"


let show_version () =
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
                   Version.release ^ " of " ^ Version.reldate ^ ")\n" );
  print_string license ;
  exit 0



let options = [
  ("-", Arg.Unit (function () -> ignore (parse_from_channel "*stdin*" stdin)),
    "Read from standard input");
  ("-V", Arg.Unit show_version, "  Show the version and exit");
  ("-version", Arg.Unit show_version, "  Show the version and exit");
  ("--version", Arg.Unit show_version, "  Show the version and exit")]

let main () =
  let action n =
    let tree = parse_from_file n in
      BackendCreol.pretty_print_program stdout tree
  in
    Arg.parse options action "cmcvalid [options] [files]"
;;

main ()
