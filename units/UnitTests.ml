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

open Arg
open OUnit

(* Show the name and the version of this program as well as its
   license information and exit. *)
let show_version () =
  (** Show the name and the version of the program and exit. *)
  print_string (Version.package ^ " " ^ Version.version ^ " (unittests)");
  exit 0

let verbose = ref false

(* A list of all command line options accepted by this program. This
   list is used by ocamls functions for parsing arguments given to the
   command line.
*)
let options = [
  ("-v", Set verbose, "  Run tests verbosely");
  ("-V", Unit show_version, "  Show the version and exit");
  ("-version", Unit show_version, "  Show the version and exit");
  ("--version", Unit show_version, "  Show the version and exit")]

(* Aggregate all tests from the different sub-modules into one place. *)
let test_fixture =
  "Tests" >::: [
    CreolTests.test_fixture ;
    UpdateDependTests.test_fixture ;
  ]

(* The main function parses the command line arguments, parses all
   input programs and executes all phases of the compilation.
*)
let main () =
  let _ = parse options (fun _ -> ()) (Sys.executable_name ^ " [options]") in
  let res = run_test_tt ~verbose:!verbose test_fixture in
  let ec =
    let p = function RSuccess _ -> true | _ -> false in
      if List.for_all p res then 0 else 1 
  in
    exit ec
  ;;

main ()
